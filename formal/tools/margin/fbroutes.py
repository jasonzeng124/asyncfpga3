#!/usr/bin/env python3
"""margin/fbroutes.py (shard C): tabulate fbslack_ctl.txt over routes (a farm request's task directories).

    python3 fbroutes.py RESULTS_DIR [--cells PAT1,PAT2,...]

For each task: its build name (build.txt), the slack of every controller matching a pattern, and the route's smallest
controller slack. Then per pattern: median, min, max over routes.
"""
import argparse, glob, os, re, statistics
ap = argparse.ArgumentParser(); ap.add_argument("dir")
ap.add_argument("--cells", default="ulink_n_falseResult_7.many.stage[0].u.ctl,ulink_n_falseResult_7.many.stage[1].u.ctl,ulink_n_index_11.many.stage[0].u.ctl,ulink_n_index_15.many.stage[0].u.ctl")
a = ap.parse_args()
pats = a.cells.split(",")
rows = []
for t in sorted(glob.glob(os.path.join(a.dir, "*")), key=lambda p: int(os.path.basename(p)) if os.path.basename(p).isdigit() else 0):
    bt, ft = os.path.join(t, "build.txt"), os.path.join(t, "fbslack_ctl.txt")
    if not (os.path.exists(bt) and os.path.exists(ft)): continue
    name = open(bt).readline().split()[0]
    sdf = re.search(r"^([0-9a-f]{8})[0-9a-f]* .*\.sdf$", open(bt).read(), re.M)
    vals = {}; mn = None
    for l in open(ft):
        f = l.split()
        if len(f) < 7 or l.startswith("#"): continue
        sl, A, B, cell = int(f[0]), int(f[3]), int(f[4]), f[5]
        if mn is None: mn = (sl, cell)
        for p in pats:
            if p in cell and p not in vals: vals[p] = (sl, A, B)
    rows.append((name, sdf.group(1) if sdf else "?", vals, mn))
print("route  sdf  " + "  ".join(p.replace("ulink_", "").replace(".many.stage", "").replace(".u.ctl", "") for p in pats) + "  route-min")
for name, sdf, vals, mn in rows:
    print("%-16s %s  %s  %s" % (name, sdf, "  ".join(("%+5d (A %d, B %d)" % vals[p]) if p in vals else "   --" for p in pats),
                                 ("%+d %s" % (mn[0], mn[1].replace("bridge_i.udut.", ""))) if mn else "--"))
for p in pats:
    xs = [v[p][0] for _, _, v, _ in rows if p in v]
    if xs: print("%s: n %d, median %+d, min %+d, max %+d ps" % (p, len(xs), statistics.median(xs), min(xs), max(xs)))
