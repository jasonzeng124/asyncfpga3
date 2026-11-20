#!/usr/bin/env python3
"""trim_plan.py CA_DIR ROUTED_JSON -- how far each delay line of a ROUTED design can be trimmed (trim_lines.py) without
taking any sized constraint below zero, from the rule's own report on that route.  Prints "MACRO=LEN ..." (the lines
worth moving), and one line per macro on stderr.

CA_DIR is a corner_audit run directory of the auto loop's rule() (rule_0.20/ and rule_0.31/, each with report.txt and
soak.sdf: the route's SDF scaled to that corner).  Why not the rule's sizes proposal: it prices a removed element at
the line's mean step, but a trimmed line is entered through its side net (bd_delay_gated: `gate`; bd_delay: `a`), so
trimming "one element" skips the anchor LUT, the first element and two wires: about two elements' worth.  Applied
as a proposal, that opened 14-16 short constraints on xorshift's route (research/data/trim/README.md).

Per trimmable chain (g[k>=1] LUT2 elements with a side input) and corner:
  t(k) = the arrival at the chain's tail from the side net's driver R when the line is entered at g[k]:
         R -> g[k]'s side pin -> g[k] -> g[k+1] ... -> tail (the routed arcs of that corner's SDF);
  t(cur) = the same for the current entry, or, untrimmed, the rising walk from R through the anchor and g[0];
  the trim to entry k removes delta(k) = t(cur) - t(k).
Each sized constraint (report.txt's "every constraint" rows, rules A E F H I K L B C, kernel only) that depends on the
line (its "depends on: MACRO(-s)") loses delta * min(1, s / L), L = the line's current delay; a line is trimmed to the
deepest entry for which every such constraint stays >= 0 at both corners, lines taken longest first, each one's loss
charged to the constraints before the next is considered.  A constraint already below zero blocks every line it depends
on.  All chains of one macro move to the same length (the most any of them can)."""
import collections, json, math, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "cells", "verify"))
import tighten as T  # noqa: E402
from pathlib import Path  # noqa: E402

SIZED = set("AEFHIKLBC")
RW = re.compile(r"^  (\S+)\s+([+-]?\d+)  (.*)$")
RE_EL = re.compile(r"^(?P<base>.+)\.chain\.g\[(?P<i>\d+)\]\.u$")


def rd_report(p):
    """research/data/converge/tools/rescatter.py's reader: key -> {margin, deps{BD_SZ_..: sens or inf}}, worst row."""
    cons, cur, on = {}, None, False
    for ln in open(p):
        if ln.startswith("every constraint"):
            on = True
            continue
        if not on:
            continue
        if ln.startswith("gaps the audits"):
            break
        m = RW.match(ln.rstrip("\n"))
        if m and not ln.startswith("             "):
            rule, mg, text = m.group(1), int(m.group(2)), m.group(3)
            if rule not in SIZED or "bridge_i.udut." not in " ".join(text.split()[:3]):
                cur = None
                continue
            k = rule + " " + " ".join(text.split()[:1])
            cur = dict(margin=mg, deps={})
            if k in cons and cons[k]["margin"] <= mg:
                cur = cons[k]
                continue
            cons[k] = cur
            continue
        m = re.match(r"^\s+depends on: (.*)$", ln)
        if m and cur is not None:
            for x in m.group(1).split(", "):
                mm = re.match(r"(\S+)\(-(\S+)\)", x.strip())
                if mm:
                    cur["deps"]["BD_SZ_" + mm.group(1)] = math.inf if mm.group(2) == "all" else float(mm.group(2))
    return cons


def macro_of(base, last_stage):
    sys.path.insert(0, HERE)
    import trim_lines as TL
    return TL.macro(TL.knob_of_base(base, last_stage))


def main():
    ca, rj = sys.argv[1], sys.argv[2]
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
    trimmable = {}
    for b, els in chains.items():
        N = max(els) + 1
        if sorted(els) != list(range(N)) or N < 2:
            continue
        if any(cells[els[k]]["attributes"].get("X_ORIG_TYPE") != "LUT2" for k in range(1, N)):
            continue
        e = max([k for k in range(1, N) if cells[els[k]]["parameters"].get("INIT") == "1100"] or [0])
        trimmable[b] = (N, e, [els[k] for k in range(N)])
    corners = [c for c in ("0.20", "0.31") if os.path.exists(os.path.join(ca, "rule_" + c, "report.txt"))]
    cons = {c: rd_report(os.path.join(ca, "rule_" + c, "report.txt")) for c in corners}
    # per corner: the routed arcs (the trimmed design's live ones) and per chain t(k) for every entry k
    tk = {}            # (corner, base) -> {k: t(k)}, k = 0 for the current untrimmed path
    for c in corners:
        edges, back, stops = T.routed_graph(Path(os.path.join(ca, "rule_" + c, "soak.sdf")))
        timing = T.Timing(edges, stops)
        for b, (N, e, insts) in trimmable.items():
            pins = {}
            for p in back:
                i = T.pin_split(p)[0]
                if i in insts:
                    pins.setdefault(i, []).append(p)
            tail = insts[-1] + "/O6"
            # the side net's driver: the source of g[N-1]'s input that is not g[N-2]
            side_src = None
            for p in pins.get(insts[-1], []):
                if T.is_output(p):
                    continue
                for s in back.get(p, ()):
                    if T.pin_split(s)[0] not in (insts[-2], insts[-1]):
                        side_src = s
            if side_src is None:
                continue
            arc = {(s, dd): w for s, lst in edges.items() for dd, w in lst}

            def chain_from(k):           # arrival at the tail from g[k]'s output, through g[k+1..N-1]
                t, prev = 0, insts[k] + "/O6"
                for j in range(k + 1, N):
                    best = None
                    for p in pins.get(insts[j], []):
                        if (prev, p) in arc and (p, insts[j] + "/O6") in arc:
                            v = arc[(prev, p)] + arc[(p, insts[j] + "/O6")]
                            best = v if best is None else min(best, v)
                    if best is None:
                        return None
                    t += best
                    prev = insts[j] + "/O6"
                return t
            row = {}
            for k in range(1, N):
                best = None
                for p in pins.get(insts[k], []):
                    if (side_src, p) in arc and p in {dd for dd, _ in edges.get(side_src, ())}:
                        w = arc[(side_src, p)]
                        lut = max([ww for dd, ww in edges.get(p, ()) if dd == insts[k] + "/O6"] or [None]) \
                            if any(dd == insts[k] + "/O6" for dd, _ in edges.get(p, ())) else None
                        if lut is None:      # the side pin's LUT arc is cut while g[k] is not the entry: use the
                            lut = 61         # site's LUT arc (every element's is the same 6-LUT arc in this SDF)
                        rest = chain_from(k)
                        if rest is not None:
                            v = w + lut + rest
                            best = v if best is None else min(best, v)
                if best is not None:
                    row[k] = best
            if e == 0:                       # untrimmed: the RISING walk from the side net's driver to the tail
                walk = timing.early(side_src)  # (the fast-fall side arcs carry only the fall: excluded, as rule A does)
                if tail in walk:
                    row[0] = walk[tail]
            tk[(c, b)] = row
    # lines, longest first; per macro the most every chain of it allows
    by_mac = collections.defaultdict(list)
    for b in trimmable:
        by_mac[macro_of(b, last_stage)].append(b)
    margin = {c: {k: v["margin"] for k, v in cons[c].items()} for c in corners}
    out, why = {}, {}
    order = sorted(by_mac, key=lambda mac: -max(tk.get((corners[-1], b), {}).get(trimmable[b][1], 0) for b in by_mac[mac]))
    for mac in order:
        bases = by_mac[mac]
        best_len = None
        charge = None
        for b in bases:
            N, e, _ = trimmable[b]
            cur_len = N - e
            ok_len, ok_charge = cur_len, {}
            for k in range(e + 1, N):     # deeper entries: shorter lines
                L_new = N - k
                fine, ch = True, {}
                for c in corners:
                    row = tk.get((c, b), {})
                    if e not in row or k not in row:
                        fine = False
                        break
                    delta = row[e] - row[k]
                    if delta <= 0:
                        continue
                    L = row[e]
                    for key, con in cons[c].items():
                        s = con["deps"].get(mac)
                        if s is None:
                            continue
                        f = 1.0 if s == math.inf or L <= 0 else min(1.0, s / L)
                        loss = delta * f
                        if margin[c][key] - loss < 0:
                            fine = False
                            break
                        ch[(c, key)] = loss
                    if not fine:
                        break
                if not fine:
                    break
                ok_len, ok_charge = L_new, ch
            if best_len is None or ok_len > best_len:      # the macro moves no further than its least trimmable chain
                best_len, charge = ok_len, ok_charge
        cur = trimmable[bases[0]][0] - trimmable[bases[0]][1]
        if best_len is not None and best_len < cur:
            out[mac] = best_len
            for (c, key), loss in charge.items():
                margin[c][key] -= loss
            why[mac] = "%d -> %d" % (cur, best_len)
        else:
            why[mac] = "kept at %d" % cur
    for mac in sorted(why):
        print("%s %s" % (mac, why[mac]), file=sys.stderr)
    print(" ".join("%s=%d" % kv for kv in sorted(out.items())))


if __name__ == "__main__":
    main()
