#!/usr/bin/env python3
"""Region factors exactly as gen.py RegionModel (efc6538) computes them, for every occupied region of a routed JSON.
usage: region_factors.py ROUTED_JSON SIGMA SEED [SIZE]"""
import json, re, sys, hashlib, math, collections
js, sigma, seed = sys.argv[1], float(sys.argv[2]), sys.argv[3]
size = int(sys.argv[4]) if len(sys.argv) > 4 else 10
cells = json.load(open(js))["modules"]["top"]["cells"]
RE = re.compile(r"^[A-Z0-9_]*?_X(\d+)Y(\d+)/")
occ = collections.Counter()
for c in cells.values():
    m = RE.match(c.get("attributes", {}).get("NEXTPNR_BEL", ""))
    if m: occ[(int(m.group(1)) // size, int(m.group(2)) // size)] += 1
def f(k):
    h = hashlib.md5(("region:%s:%d:%d" % (seed, k[0], k[1])).encode()).digest()
    u1 = (int.from_bytes(h[:8], "big") + 1) / 2.0 ** 64; u2 = int.from_bytes(h[8:], "big") / 2.0 ** 64
    return 1 + sigma * math.sqrt(-2 * math.log(u1)) * math.cos(2 * math.pi * u2)
fs = sorted((f(k), k, n) for k, n in occ.items())
print(f"seed {seed} sigma {sigma}: {len(fs)} occupied regions; min {fs[0][0]:.3f} max {fs[-1][0]:.3f}")
for x, k, n in fs[:5]: print(f"  low  region {k} cells {n} factor {x:.3f}  (N={(x-1)/sigma:+.2f})")
for x, k, n in fs[-3:]: print(f"  high region {k} cells {n} factor {x:.3f}  (N={(x-1)/sigma:+.2f})")
print("  regions with factor<=0:", sum(1 for x,_,_ in fs if x <= 0), " <0.5:", sum(1 for x,_,_ in fs if x < 0.5))
