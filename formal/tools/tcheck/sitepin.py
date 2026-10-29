#!/usr/bin/env python3
"""C-10g: how far nextpnr's SDF interconnect number is from prjxray, per PHYSICAL LUT pin
(the 10b site-pin effect, measured on a shipped route).  Samples N LUT-pin nets.
    python3 sitepin.py SEED [N]   -> results/sitepin_SEED.tsv"""
import os, pathlib, random, sys, statistics
from collections import defaultdict
sys.argv, (seed, N) = [sys.argv[0]], (sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 4000)
import extract as E
H = pathlib.Path(__file__).resolve().parent
T, R, F = E.load_rules(H / f"build/tree_{seed}/cells")
O = H / f"build/tree_{seed}/cells/build/hw/gcd_hw"
edges, *_ = T.parse_sdf(O / "gcd_hw.sdf")
P = E.Prjx(R, F, O / "gcd_hw.fasm", O / "gcd_hw_routed.json")
arcs = [(s, d, w) for s, l in edges.items() if T.is_output(s) for d, w in l
        if not T.is_output(d) and d.rsplit("/", 1)[1] in ("A1", "A2", "A3", "A4", "A5", "A6")]
random.seed(1); random.shuffle(arcs)
by = defaultdict(list)
for s, d, w in arcs[:N]:
    c = P.interconnect(s, d)
    if c is None:
        continue
    ip = P.inpin.get((s, d))
    sp = [R.pick(ip.get_intrinsic_delays(), k) * 1e3 for k in range(4)] if ip else [0] * 4
    mux = any(x > 0 for x in P.hops.get((s, d), ([0] * 4, None))[0])
    by[d.rsplit("/", 1)[1]].append((w, c[3], c[0], sp[3], mux))
TAG = os.environ.get("SITEPIN_TAG", "_")   # C-10m: e.g. "10m_" -> results/sitepin10m_SEED.tsv
out = open(H / f"results/sitepin{TAG}{seed}.tsv", "w")
out.write("pin\tn\tsdf_mean\tslow_max_mean\tfast_min_mean\tsitepin_slow_max\tdelta(slow_max-sdf)_mean\tdelta_p10\tdelta_p90"
          "\tdelta_max\tfast_min-sdf_mean\tn_via_outmux\tdelta_mean_via_outmux\n")
for p in sorted(by):
    xs = by[p]
    ds = sorted(x[1] - x[0] for x in xs)
    row = (p, len(xs), round(statistics.mean(a for a, *_ in xs)), round(statistics.mean(x[1] for x in xs)),
           round(statistics.mean(x[2] for x in xs)), round(statistics.mean(x[3] for x in xs)),
           round(statistics.mean(ds)), round(ds[len(ds) // 10]), round(ds[9 * len(ds) // 10]),
           # C-10m: the max, the fast-corner side and the nets through an OUTMUX (driver hop)
           round(ds[-1]), round(statistics.mean(c - a for a, _, c, *_ in xs)), sum(1 for x in xs if x[4]),
           round(statistics.mean([b - a for a, b, _, _, m in xs if m] or [0])))
    out.write("\t".join(map(str, row)) + "\n")
out.close()
print(open(H / f"results/sitepin{TAG}{seed}.tsv").read())
