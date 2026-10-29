#!/usr/bin/env python3
"""C-10g: how far nextpnr's SDF interconnect number is from prjxray, per PHYSICAL LUT pin
(the 10b site-pin effect, measured on a shipped route).  Samples N LUT-pin nets.
    python3 sitepin.py SEED [N]   -> results/sitepin_SEED.tsv"""
import pathlib, random, sys, statistics
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
    by[d.rsplit("/", 1)[1]].append((w, c[3], c[0], sp[3]))
out = open(H / f"results/sitepin_{seed}.tsv", "w")
out.write("pin\tn\tsdf_mean\tslow_max_mean\tfast_min_mean\tsitepin_slow_max\tdelta(slow_max-sdf)_mean\tdelta_p10\tdelta_p90\n")
for p in sorted(by):
    xs = by[p]
    ds = sorted(b - a for a, b, _, _ in xs)
    row = (p, len(xs), round(statistics.mean(a for a, *_ in xs)), round(statistics.mean(b for _, b, _, _ in xs)),
           round(statistics.mean(c for _, _, c, _ in xs)), round(statistics.mean(e for *_, e in xs)),
           round(statistics.mean(ds)), round(ds[len(ds) // 10]), round(ds[9 * len(ds) // 10]))
    out.write("\t".join(map(str, row)) + "\n")
out.close()
print(open(H / f"results/sitepin_{seed}.tsv").read())
