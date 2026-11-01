#!/usr/bin/env python3
"""T6: smallest T for which a finite trace satisfies Spec.ArbOK(T) on [0, TEND] (my tsim --out JSON).
For each arbiter: maximal intervals where every input in a.ins is constant; q must be constant on [t1+T, t2].
usage: arbcheck.py RUN.json ARBS.json AUD_NET.json"""
import json, sys
R = json.load(open(sys.argv[1])); arbs = json.load(open(sys.argv[2])); an = json.load(open(sys.argv[3]))["nodes"]
idx = {n: i for i, n in enumerate(an)}; H = R["hist"]; TEND = R["T"]
def chg(n):  # change times (value differs from the previous ps)
    return [t for t, v in H[str(n)][1]]
worst = 0
for j, a in enumerate(arbs):
    q = idx[a["q"]]; ins = [idx[x] for x in a["ins"]]
    cuts = sorted(set(t for n in ins for t in chg(n)))
    qc = chg(q)
    bounds = [0] + cuts + [TEND + 1]
    need = 0; where = None
    for s, e in zip(bounds, bounds[1:]):     # inputs constant on [s, e-1]
        us = [u for u in qc if s < u <= e - 1]
        if us and us[-1] - s > need: need, where = us[-1] - s, (s, e - 1, len(us))
    late = [u for u in qc if u > 600000]
    print("arb%d q=%s: input changes %d, q changes %d (%d after 600 ns); min T for ArbOK on [0,%d] = %d ps %s"
          % (j, a["q"], len(cuts), len(qc), len(late), TEND, need, where or ""))
    worst = max(worst, need)
print("ArbOK(T) holds on this finite trace for every T >= %d ps" % worst)
