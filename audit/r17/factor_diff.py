#!/usr/bin/env python3
"""Per-arc drawn delay factor = scattered netlist_baked.v delay / unscattered band netlist_baked.v delay (same route,
same gen.py), line by line.  usage: factor_diff.py BASE_BAKED SCAT_BAKED [cell_or_ic ...] """
import re, sys
P = re.compile(r"\.(T\w+|D)\((\d+)\)")
def load(f):
    d = {}
    for ln in open(f):
        m = re.match(r"\s*(\w+) #\((.*)\) (\w+) \(", ln)
        if m: d[m.group(3)] = (m.group(1), {k: int(v) for k, v in P.findall(m.group(2)) if k not in ("TSU", "THD")})
    return d
b, s = load(sys.argv[1]), load(sys.argv[2])
want = set(sys.argv[3:])
rs = []; zero = 0
for n, (t, pb) in b.items():
    ps = s[n][1]
    for k, v in pb.items():
        if v > 0:
            r = ps[k] / v; rs.append((r, n, t, k, v, ps[k]))
            if ps[k] == 0: zero += 1
        if n in want: print(f"{n} {t} {k}: base {v} scat {ps[k]} factor {ps[k]/v if v else float('nan'):.3f}")
if want: sys.exit()
rs.sort()
import statistics
q = lambda p: rs[int(p * (len(rs) - 1))][0]
print(f"arcs with base>0: {len(rs)}; clamped to 0: {zero}; factor<0.1: {sum(r[0]<0.1 for r in rs)}; <0.25: {sum(r[0]<0.25 for r in rs)}; >2: {sum(r[0]>2 for r in rs)}; >3: {sum(r[0]>3 for r in rs)}")
print(f"quantiles 0.1% {q(.001):.3f} 1% {q(.01):.3f} 50% {q(.5):.3f} 99% {q(.99):.3f} 99.9% {q(.999):.3f}; min {rs[0][0]:.3f} max {rs[-1][0]:.3f}")
