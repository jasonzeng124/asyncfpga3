#!/usr/bin/env python3
"""C-10m: arc-by-arc cross-check of tcheck's prjxray front end (extract.Prjx) against the
auditor's independent model (audit/tc/xrc.py on origin/claude/audit, which shares no code
with extract.py / prjxdelay / fasm2lean).  Reporting only; no verdict depends on it.

    python3 xrcarcs.py BUILD_DIR TOP CELLS_DIR XRC_DIR TAG
      BUILD_DIR  holds TOP.sdf, TOP_routed.json, TOP.fasm
      XRC_DIR    a directory holding xrc.py (git show origin/claude/audit:audit/tc/xrc.py)
      -> results/xrcarcs_TAG.tsv (per class: n, mean/max |diff| per corner, n within 15 ps)
         results/xrcarcs_TAG_out.tsv (every arc outside 15 ps in some corner, with both values)
XRC_NOMUX=1 in the environment makes xrc drop its OUTMUX term (the C-10g model)."""
import os
import pathlib
import re
import statistics
import sys
from collections import defaultdict

bd, top, cells, xdir, tag = sys.argv[1:6]
sys.argv = [sys.argv[0]]
H = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(H))
import extract as E  # noqa: E402

T, R, F = E.load_rules(pathlib.Path(cells))
bd = pathlib.Path(bd)
edges, *_ = T.parse_sdf(bd / f"{top}.sdf")
P = E.Prjx(R, F, bd / f"{top}.fasm", bd / f"{top}_routed.json")
sys.path.insert(0, xdir)
import xrc as X  # noqa: E402
XR = X.Route(str(bd))

stats = defaultdict(list)
outl = []
n_tc = n_x = n_both = 0
for s, lst in edges.items():
    for d, w in lst:
        same = T.pin_split(s)[0] == T.pin_split(d)[0] and not T.is_output(s)
        try:
            tc = P.iopath(s, d) if same else P.interconnect(s, d)
        except Exception:        # noqa: BLE001  (reporting only)
            tc = None
        try:
            xr = X.route_arc(XR, s, d)
        except Exception:        # noqa: BLE001
            xr = None
        n_tc += tc is not None
        n_x += xr is not None
        if tc is None or xr is None:
            continue
        n_both += 1
        if same:
            cls = "cell:" + ("LUT" if re.match(r"A[1-6]$", T.pin_split(s)[1]) else T.pin_split(d)[1])
        else:
            dh = P.hops.get((s, d), ([0] * 4, None))[0]
            db_ = P.drv_bel(*s.rsplit("/", 1)) or "?"
            if any(x > 0 for x in dh):
                cls = f"net via OUTMUX ({re.sub(r'^[a-d]', 'x', db_)})"
            else:
                cls = "net direct (" + re.sub(r"^[a-d]", "x", db_) + ")"
        diff = [a - b for a, b in zip(tc, xr)]
        stats[cls].append(diff)
        if any(abs(x) > 15 for x in diff):
            outl.append((cls, s, d, w, [round(x) for x in tc], [round(x) for x in xr], [round(x) for x in diff]))

o = open(H / f"results/xrcarcs_{tag}.tsv", "w")
o.write(f"# arcs: tcheck resolves {n_tc}, xrc resolves {n_x}, both {n_both}; XRC_NOMUX={os.environ.get('XRC_NOMUX', '')}\n")
o.write("class\tn\twithin15(all 4 corners)\tmean diff fmin/fmax/smin/smax (tc-xrc)\tmax |diff|\n")
for cls, D in sorted(stats.items(), key=lambda x: -len(x[1])):
    o.write(f"{cls}\t{len(D)}\t{sum(all(abs(x) <= 15 for x in d) for d in D)}\t"
            + "/".join(str(round(statistics.mean(d[i] for d in D), 1)) for i in range(4)) + "\t"
            + "/".join(str(round(max(abs(d[i]) for d in D))) for i in range(4)) + "\n")
o.close()
with open(H / f"results/xrcarcs_{tag}_out.tsv", "w") as o:
    o.write("class\tsrc\tdst\tsdf\ttcheck fmin/fmax/smin/smax\txrc\tdiff\n")
    for r in sorted(outl, key=lambda r: -max(abs(x) for x in r[6])):
        o.write("\t".join([r[0], r[1], r[2], str(r[3])] + ["/".join(map(str, x)) for x in r[4:]]) + "\n")
print(open(H / f"results/xrcarcs_{tag}.tsv").read())
print(f"outliers (>15 ps in some corner): {len(outl)}")
