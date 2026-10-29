#!/usr/bin/env python3
"""C-10g diagnostics (UNTRUSTED, explanation only): critical paths of one instance.
    python3 diag.py OBL.tc 'LABEL PREFIX' [VARIANT]   (default fastG)
For the variant: the path to the request node achieving its EARLIEST change and the
path to the data node achieving the LATEST, each arc with its interval in every
variant (columns), so the corner/site-pin/fallback contribution can be read off."""
import sys
from collections import defaultdict
tc, pre = sys.argv[1], sys.argv[2]
var = sys.argv[3] if len(sys.argv) > 3 else "fastG"
inst = {}
cur = None
for line in open(tc):
    w = line.split()
    if w[0] == "inst":
        lab = " ".join(w[1:])
        if lab.startswith(pre):
            v = w[-2]; cur = {"arcs": [], "data": []}; inst[v] = cur; cur["label"] = lab
        else:
            cur = None
    elif cur is None:
        continue
    elif w[0] == "req":
        cur["req"] = int(w[1])
    elif w[0] == "data":
        cur["data"] += [int(x) for x in w[1:]]
    elif w[0] == "arc":
        cur["arcs"].append(tuple(map(int, w[1:])))
I = inst[var]
print(I["label"])
lo, hi, plo, phi = {0: 0}, {0: 0}, {}, {}
for a, b, l, h in sorted(I["arcs"]):
    if a in lo:
        if b not in lo or lo[a] + l < lo[b]:
            lo[b] = lo[a] + l; plo[b] = (a, l, h)
        if b not in hi or hi[a] + h > hi[b]:
            hi[b] = hi[a] + h; phi[b] = (a, l, h)
tab = {v: {(a, b): (l, h) for a, b, l, h in inst[v]["arcs"]} for v in inst}
VS = [v for v in ("sdf", "sdfband", "fast", "slow", "fastG", "slowG") if v in inst]
def show(n, P, what):
    path = []
    while n in P:
        a = P[n][0]; path.append((a, n)); n = a
    path.reverse()
    print(f"  {what}: " + "  ".join(VS))
    tot = defaultdict(int)
    for a, b in path:
        cells = []
        for v in VS:
            l, h = tab[v][(a, b)]; cells.append(f"{l}..{h}")
            tot[v] += (l if what == "req(earliest)" else h)
        print(f"    {a:>4}->{b:<4} " + "  ".join(f"{c:>11}" for c in cells))
    print("    total " + "  ".join(f"{tot[v]:>11}" for v in VS))
show(I["req"], plo, "req(earliest)")
d = max((x for x in I["data"] if x in hi), key=lambda x: hi[x])
show(d, phi, "data(latest)")
