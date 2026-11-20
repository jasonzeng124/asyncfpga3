#!/usr/bin/env python3
"""trim_lines.py ROUTED_JSON FASM_IN OUT_JSON OUT_FASM [--partial] MACRO=LEN [MACRO=LEN ...] -- shorten matched delay lines of a ROUTED
design without re-placing or re-routing it: a LUT INIT edit per line, in the routed JSON and in the FASM.

A line is a bd_delay / bd_delay_gated chain (cells/rtl/bd_latch.v): g[0] = LUT1(s[0]), g[k>=1] = LUT2(s[k], side) with
side = the line's input (FASTFALL: AND, INIT 1000; FASTRISE: OR, 1110; bd_delay_gated: AND with `gate`).  Making g[i]
pass its side input (INIT 1100: O = I1) makes g[i] the line's entry: the line is then N - i elements long, with the
same edge behaviour (AND line: rise through g[i..N-1], fall at once; OR line: rise at once, fall through them).  The
elements before g[i] stay placed and routed and drive nothing that matters (g[i] no longer reads s[i]).  So any line
of N >= 2 elements of LUT2s can be shortened to any length 1..N after routing, by bits alone; only lengthening needs a
new route.  A symmetric line (LUT1 elements, no side input) cannot, and is refused.

MACRO is a sizes.vh macro (BD_SZ_..., as research/tools/corner_audit.py names lines: knob_of_base); every chain that
maps to it is trimmed (a pipe's _SDELAY covers several stages' rdly, a link's _UACK every stage's uack).  LEN is the new
length in elements.  The FASM's LUT INIT for each touched site is recomputed from the edited cells with
cells/verify/fasm_audit.py's expected_lut_bits (the same encoding nextpnr's fasm.cc writes, X_ORIG_PORT pins included).
Why: research/data/placekeep/README.md -- every size change otherwise means a fresh placement, a fresh draw of every
other constraint's margin, and a finish phase that keeps each raised line at the largest need any of its routes had.
Prints one line per chain trimmed and a summary; exit 1 on any refusal."""
import json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "cells", "verify"))
sys.path.insert(0, os.path.join(REPO, "research", "tools"))
import fasm_audit as FA  # noqa: E402

RE_EL = re.compile(r"^(?P<base>.+)\.chain\.g\[(?P<i>\d+)\]\.u$")
AND, OR, SIDE = "1000", "1110", "1100"


def knob_of_base(base, last_stage):
    """corner_audit.knob_of_base, copied (corner_audit.py runs its CLI on import)."""
    m = re.match(r"^(.*)_uport\.(.*)$", base)
    if m:
        base = m.group(1) + "." + m.group(2)
    m = re.match(r"^(.*)\.udly_s$", base)
    if m:
        return m.group(1) + "_short"
    m = re.match(r"^(.*)\.udly$", base)
    if m:
        return m.group(1)
    m = re.match(r"^(.*?)(?:\.(?:one|many\.stage\[\d+\])\.u)?\.uack$", base)
    if m:
        return m.group(1) + ".uack"
    m = re.match(r"^(.*)\.many\.stage\[(\d+)\]\.u\.rdly$", base)
    if m:
        return m.group(1) if int(m.group(2)) == last_stage.get(m.group(1), -1) else m.group(1) + ".sdelay"
    m = re.match(r"^(.*?)(?:\.one\.u)?\.rdly$", base)
    if m:
        return m.group(1)
    return base


def macro(path):
    return "BD_SZ_" + re.sub(r"[^A-Za-z0-9]", "_", path).upper()


def list_lines(rj):
    """--list ROUTED_JSON: one line per sizes macro, "MACRO<TAB>trimmable|symmetric<TAB>N" (N: its shortest chain's
    length; trimmable: every chain of the macro has side-input LUT2s at g[1..N-1], so trim_lines.py can shorten it)."""
    d = json.load(open(rj))
    top = [m for m in d["modules"].values() if any("NEXTPNR_BEL" in c.get("attributes", {}) for c in m.get("cells", {}).values())][0]
    cells = top["cells"]
    chains = {}
    for n in cells:
        m = RE_EL.match(n)
        if m and n.startswith("bridge_i.udut."):
            chains.setdefault(m.group("base"), {})[int(m.group("i"))] = n
    last_stage = {}
    for b in chains:
        m = re.match(r"^(.*)\.many\.stage\[(\d+)\]\.u\.rdly$", b)
        if m:
            last_stage[m.group(1)] = max(last_stage.get(m.group(1), -1), int(m.group(2)))
    # A 1-element line shows no type (g[0] is a LUT1 in every kind).  Two kinds are side-input lines by construction:
    # a link's acknowledge line (rtl/bd_link.v: uack is FASTFALL / FASTRISE in every variant) and a bdc compute unit's
    # request line (bdc/compute.py request_delay: bd_delay_gated under BDC_FASTFALL, the default); any other
    # 1-element line is "unknown".
    gated = re.compile(r"^bridge_i\.udut\.u(?:addi|subi|muli|cmpi|andi|ori|xori|shli|shrsi|shrui|select|divui|divsi|"
                       r"remui|remsi|minui|maxui|minsi|maxsi)\d+\.udly$")
    out = {}
    for b, els in chains.items():
        mac = macro(knob_of_base(b, last_stage))
        N = max(els) + 1
        if N == 1:
            k = "trimmable" if (b.endswith(".uack") or gated.match(b)) else "unknown"
        else:
            ok = sorted(els) == list(range(N)) and all(
                cells[els[i]]["attributes"].get("X_ORIG_TYPE") == "LUT2" and cells[els[i]]["parameters"].get("INIT") in (AND, OR, SIDE)
                for i in range(1, N))
            k = "trimmable" if ok else "symmetric"
        t, n = out.get(mac, (k, N))
        rank = {"symmetric": 0, "unknown": 1, "trimmable": 2}   # a macro is as trimmable as its least trimmable chain
        out[mac] = (min(t, k, key=rank.get), min(n, N))
    for mac in sorted(out):
        print("%s\t%s\t%d" % (mac, out[mac][0], out[mac][1]))


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--list":
        return list_lines(sys.argv[2])
    if len(sys.argv) < 6:
        sys.exit(__doc__)
    partial = "--partial" in sys.argv          # apply what can be trimmed, list the rest (exit 0)
    sys.argv = [x for x in sys.argv if x != "--partial"]
    rj, fin, oj, of = sys.argv[1:5]
    want = {}
    for a in sys.argv[5:]:
        k, v = a.split("=")
        want[k] = int(v)
    d = json.load(open(rj))
    top = [m for m in d["modules"].values() if any("NEXTPNR_BEL" in c.get("attributes", {}) for c in m.get("cells", {}).values())][0]
    cells = top["cells"]
    chains = {}
    for n in cells:
        m = RE_EL.match(n)
        if m and n.startswith("bridge_i.udut."):
            chains.setdefault(m.group("base"), {})[int(m.group("i"))] = n
    last_stage = {}
    for b in chains:
        m = re.match(r"^(.*)\.many\.stage\[(\d+)\]\.u\.rdly$", b)
        if m:
            last_stage[m.group(1)] = max(last_stage.get(m.group(1), -1), int(m.group(2)))
    by_macro = {}
    for b in chains:
        by_macro.setdefault(macro(knob_of_base(b, last_stage)), []).append(b)
    touched, bad, done = set(), [], []
    for mac, L in sorted(want.items()):
        bases = by_macro.get(mac)
        if not bases:
            bad.append("%s: no chain maps to it" % mac)
            continue
        for b in sorted(bases):
            els = chains[b]
            N = max(els) + 1
            if sorted(els) != list(range(N)):
                bad.append("%s: chain %s has gaps %s" % (mac, b, sorted(els)))
                continue
            cur = N
            for i in range(1, N):                       # an earlier trim: the entry is the first g[i] that passes side
                if cells[els[i]]["parameters"].get("INIT") == SIDE:
                    cur = N - i
            if L == cur:
                continue
            if L < 1 or L > N:
                bad.append("%s: %s has %d elements, %d asked (a trim can only shorten, to >= 1)" % (mac, b, N, L))
                continue
            i = N - L
            # restore any earlier entry first, then set the new one
            for k in range(1, N):
                c = cells[els[k]]
                if c["parameters"].get("INIT") == SIDE:
                    c["parameters"]["INIT"] = c["attributes"].get("BD_TRIM_WAS", AND)
                    touched.add(els[k])
            if i == 0:
                done.append("%s %s: %d -> %d (restored)" % (mac, b, cur, L))
                continue
            c = cells[els[i]]
            if c["attributes"].get("X_ORIG_TYPE") != "LUT2" or c["parameters"].get("INIT") not in (AND, OR):
                bad.append("%s: %s g[%d] is %s INIT %s, not a side-input LUT2 (a symmetric line cannot be trimmed)"
                           % (mac, b, i, c["attributes"].get("X_ORIG_TYPE"), c["parameters"].get("INIT")))
                continue
            c["attributes"]["BD_TRIM_WAS"] = c["parameters"]["INIT"]
            c["parameters"]["INIT"] = SIDE
            touched.add(els[i])
            done.append("%s %s: %d -> %d (entry g[%d], was %s)" % (mac, b, cur, L, i, c["attributes"]["BD_TRIM_WAS"]))
    for x in done:
        print("trim " + x)
    if bad:
        for x in bad:
            print("REFUSED " + x)
        if not partial:
            sys.exit(1)
    # the FASM: every LUT site holding a touched cell gets its INIT recomputed from the (edited) cells
    sites = FA.load_sites()
    slots = {}
    for cn, c in cells.items():
        m = FA.RE_BEL.match(c["attributes"].get("NEXTPNR_BEL", "")) if c["type"] == "SLICE_LUTX" else None
        if m:
            slots.setdefault((m.group(1), m.group(2)), {})[m.group(3)] = (cn, c)
    repl = {}
    for (site, letter), slot in slots.items():
        if not any(cn in touched for cn, _ in slot.values()):
            continue
        lut6 = slot.get("6", (None, None))[1]
        lut5 = slot.get("5", (None, None))[1]
        feat = "%s.%sLUT.INIT[63:0]" % (FA.slice_prefix(site, sites), letter)
        repl[feat] = FA.expected_lut_bits(lut6, lut5)
    out, changed, seen = [], 0, set()
    for ln in open(fin).read().splitlines():
        name = ln.split("=", 1)[0].strip()
        if name in repl:
            new = "%s = 64'b%s" % (name, format(repl[name], "064b"))
            changed += new != ln
            ln = new
            seen.add(name)
        out.append(ln)
    for name in sorted(set(repl) - seen):              # a site whose INIT was all zero has no line: add it
        if repl[name]:
            out.append("%s = 64'b%s" % (name, format(repl[name], "064b")))
            changed += 1
    open(of, "w").write("\n".join(out) + "\n")
    json.dump(d, open(oj, "w"), indent=None)
    print("trim_lines: %d chain(s) trimmed, %d LUT cell(s) edited, %d FASM LUT INIT line(s) changed"
          % (len(done), len(touched), changed))


if __name__ == "__main__":
    main()
