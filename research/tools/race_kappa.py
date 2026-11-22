#!/usr/bin/env python3
"""race_kappa.py ARCS_TSV SPECDIR [TARGET] -- formal's split-corner bound on each latch-fed steer race of a route, and
how many request-line elements would bring it to TARGET (auto_size.sh AUTO_RACE_KAPPA; formal B32 / B36).

The races are the ones research/tools/race_find.py found and wrote a spec for (SPECDIR: its third argument; ARCS_TSV:
cells/gls/fid/xray_delay.py --arcs on the same route). A spec's S arcs are the condition path (ctl -> the link latch ->
the steer) and its F arcs the request path (ctl -> the link's request line -> the join -> the steer).

    kappa = min over the corners c in {fast, slow} of (F_c - S_c) / (F_c + S_c),
            F_c = the request path with every arc at its corner-c MINIMUM,
            S_c = the condition path with every arc at its corner-c MAXIMUM.

This is formal's "ctl-term kappa_lo" (formal/tools-B/auto/steersafe.py: R = the request side at minimum arcs, D = the
condition side at maximum arcs, min over corners of (R - D) / (R + D)): each side may sit anywhere in its prjxray range
at one corner, independently. It is more pessimistic than the draw model race_mc.py prices (the two sides' routing
shares one band there, and a race passes at AUTO_RACE_Z sd of the model's scatter). Why use it anyway: over the 32
distinct latch-fed races formal screened on flow v10 / v11 routes (B32), 9 of the 10 with ctl-term kappa_lo <= 0.125
lost formal's race-only adversary inside kappa 0.20 and 1 of the 22 above 0.129 did; and two rule-CLEAN routes whose
race passed AUTO_RACE_Z=4.5 lose it at kappa 0.03 (v10 sqrtsub s4: +55 ps split slack; v11 test_flatten_array s2: +1 ps,
z 4.72 in the draw model). The ring measurements' median model error is 8.5 % (CLAUDE.md), so an adversary failure at
a few % is inside what the model cannot rule out; a delay too long only costs time.

Elements to add, per corner: ceil((S_c (1 + T) / (1 - T) - F_c) / e_c), e_c = the median corner-c minimum of one
delay-line element on this route (a chain LUT's IO arc plus the IC arc from the previous element: every
`*.chain.g[k].u` -> `g[k+1]` pair in ARCS_TSV); the larger of the two corners, 0 when the race already meets T.
An estimate: the next route places the line again (race_pad.py pads at least one element; the loop re-checks the
race on the route it builds).

Prints one line per race: "<steer> link <L>: kappa K (fast Kf: F f / S s ps; slow Ks: F f / S s ps)", with TARGET
" | target T: +N (element ef / es ps)[, short D ps]" (D: the larger corner's shortfall of F against S (1 + T) / (1 - T)).
Checked 2026-11-21 against formal B35 on the guarded lfsrfind s1 route (g10, sdf d5c91be0): ucond_br4's split slack F - S
+188 / +523 ps here, +189 / +524 in formal's steersafe; sqrtsub g10 s1 +1763-1766 / +4169-4203 here, +1772 / +4212."""
import glob
import math
import os
import re
import statistics as st
import sys


def load_arcs(tsv):
    arcs, hdr = [], None
    for ln in open(tsv):
        f = ln.rstrip("\n").split("\t")
        if hdr is None:
            hdr = f
            continue
        d = dict(zip(hdr, f))
        if d.get("kind") in ("IC", "IO"):
            arcs.append(d)
    return arcs


def elem_delay(arcs):
    """median corner minimum of one delay-line element: IO of g[k+1] + the IC g[k] -> g[k+1]"""
    io = {}
    for a in arcs:
        if a["kind"] == "IO" and re.search(r"\.chain\.g\[\d+\]\.u/A\d$", a["src"]):
            io.setdefault(a["src"].rpartition("/")[0], []).append(a)
    per = {"fast": [], "slow": []}
    for a in arcs:
        if a["kind"] != "IC":
            continue
        ms = re.match(r"^(.*\.chain\.g\[)(\d+)(\]\.u)/O6$", a["src"])
        md = re.match(r"^(.*\.chain\.g\[)(\d+)(\]\.u)/A\d$", a["dst"])
        if not (ms and md) or ms.group(1) != md.group(1) or int(md.group(2)) != int(ms.group(2)) + 1:
            continue
        inst = a["dst"].rpartition("/")[0]
        outs = [b for b in io.get(inst, []) if b["src"] == a["dst"]]
        if not outs:
            continue
        b = outs[0]
        per["fast"].append(int(a["fast_min_ps"]) + int(b["fast_min_ps"]))
        per["slow"].append(int(a["slow_min_ps"]) + int(b["slow_min_ps"]))
    return {c: (st.median(v) if v else None) for c, v in per.items()}


def main():
    tsv, sd = sys.argv[1], sys.argv[2]
    target = float(sys.argv[3]) if len(sys.argv) > 3 else None
    arcs = load_arcs(tsv)
    e = None
    for sp in sorted(glob.glob(os.path.join(sd, "*.txt"))):
        head, rules = "", []
        for ln in open(sp):
            if ln.startswith("#"):
                head = head or ln
                continue
            w = ln.split()
            if len(w) >= 4 and w[0] in ("S", "F"):
                rules.append((w[0], w[1], re.compile(w[2]), re.compile(w[3]), ln.strip()))
        m = re.match(r"# (\S+) condition (\S+) \(latch (\S+)\.lat\.odd\.u\)", head)
        if not m or not rules:
            print("%s: not a race_find.py spec" % os.path.basename(sp))
            continue
        steer = m.group(1).replace("bridge_i.udut.", "")
        link = m.group(3).replace("bridge_i.udut.", "")
        tot = {("S", "fast"): 0, ("S", "slow"): 0, ("F", "fast"): 0, ("F", "slow"): 0}
        bad = None
        for side, kind, rs, rd, txt in rules:
            hit = [a for a in arcs if a["kind"] == kind and rs.fullmatch(a["src"]) and rd.fullmatch(a["dst"])]
            if len(hit) != 1:
                bad = "%d arcs match '%s'" % (len(hit), txt)
                break
            a = hit[0]
            for c in ("fast", "slow"):
                tot[(side, c)] += int(a["%s_%s_ps" % (c, "max" if side == "S" else "min")])
        if bad:
            print("%s link %s: skipped (%s)" % (steer, link, bad))
            continue
        k = {}
        for c in ("fast", "slow"):
            f, s = tot[("F", c)], tot[("S", c)]
            k[c] = (f - s) / float(f + s) if f + s else 0.0
        kap = min(k.values())
        out = "%s link %s: kappa %.3f (fast %.3f: F %d / S %d ps; slow %.3f: F %d / S %d ps)" % (
            steer, link, kap, k["fast"], tot[("F", "fast")], tot[("S", "fast")], k["slow"], tot[("F", "slow")],
            tot[("S", "slow")])
        if target is not None:
            if e is None:
                e = elem_delay(arcs)
            need, short = 0, 0
            for c in ("fast", "slow"):
                deficit = tot[("S", c)] * (1 + target) / (1 - target) - tot[("F", c)]
                if deficit > 0:
                    # no chain pair on the route: 200 / 480 ps, below every element measured (2026-11-21: 265-267 /
                    # 633-642 ps on lfsrfind / sqrtsub g10 s1), so the guess errs to more elements
                    ec = e[c] or (200 if c == "fast" else 480)
                    need = max(need, int(math.ceil(deficit / ec)))
                    short = max(short, int(math.ceil(deficit)))
            out += " | target %.2f: +%d (element %s / %s ps)%s" % (target, need, e["fast"], e["slow"],
                                                                   ", short %d ps" % short if short else "")
        print(out)


if __name__ == "__main__":
    main()
