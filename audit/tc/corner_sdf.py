#!/usr/bin/env python3
"""Write one single-valued SDF per prjxray corner value (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) from a route,
using the auditor's xrc.py model for every LUT-pin interconnect arc and every LUT cell arc it resolves.
Unresolved arcs (FF/CARRY4/MUXF/DSP/IO cell arcs, non-LUT sinks, constant nets) are scaled by the median
model/SDF ratio of the resolved arcs of the same class at that corner (an approximation, counted).
The project's rule scripts can then be run unchanged on a consistent-corner SDF.
    python3 corner_sdf.py ROUTE_DIR OUT_DIR      (OUT_DIR outside the repo: these are SDF copies)"""
import sys, os, re, statistics
sys.path.insert(0, "/home/user/asyncfpga3/audit/tc")
import xrc
odir, outd = sys.argv[1:3]
os.makedirs(outd, exist_ok=True)
R = xrc.Route(odir)
sdfp = [os.path.join(odir, f) for f in os.listdir(odir) if f.endswith(".sdf")][0]
un = lambda s: s.replace("\\", "")
RI = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RO = re.compile(r"(\(IOPATH\s+(\S+)\s+(\S+)\s+)\((\d+):(\d+):(\d+)\)\s*\((\d+):(\d+):(\d+)\)")
RC = re.compile(r"(\(INTERCONNECT\s+(\S+)\s+(\S+)\s+)\((\d+):(\d+):(\d+)\)\s*\((\d+):(\d+):(\d+)\)")


def ic_val(src, dst):
    cs, ps = src.rsplit("/", 1); cd, pd = dst.rsplit("/", 1)
    if cd in R.cells and re.fullmatch(r"A[1-6]", pd) and "LUT" in R.cells[cd]["type"]:
        b = R.cells[cd]["connections"].get(pd, [None])[0]
        if R.driver.get(b) == (cs, ps):
            n, s = R.sink_of_cellpin(cd, pd)
            if s is not None and n.ok:
                return s["d"]
    return None


def io_val(inst, a, z):
    if inst in R.cells and re.fullmatch(r"A[1-6]", a) and "LUT" in R.cells[inst]["type"]:
        return R.lut_arc(inst, a, z)
    return None


lines = open(sdfp).read().splitlines()
vals, ratios = [], {"ic": [[] for _ in range(4)], "io": [[] for _ in range(4)]}
inst = None
for i, line in enumerate(lines):
    m = RI.search(line)
    if m:
        inst = un(m.group(1)); continue
    m = RC.search(line)
    if m:
        v = ic_val(un(m.group(2)), un(m.group(3))); d = int(m.group(4))
        vals.append((i, "ic", m, v, d))
        if v and d > 0:
            for k in range(4): ratios["ic"][k].append(v[k] / d)
        continue
    m = RO.search(line)
    if m and inst is not None:
        v = io_val(inst, m.group(2), m.group(3)); d = int(m.group(4))
        vals.append((i, "io", m, v, d))
        if v and d > 0:
            for k in range(4): ratios["io"][k].append(v[k] / d)
med = {c: [statistics.median(ratios[c][k]) for k in range(4)] for c in ratios}
nres = sum(1 for x in vals if x[3]); print(f"resolved {nres} of {len(vals)} arcs; median ratios {med}")
for k, nm in enumerate(("fmin", "fmax", "smin", "smax")):
    out = list(lines)
    for i, cls, m, v, d in vals:
        x = round(v[k]) if v else round(d * med[cls][k])
        out[i] = lines[i][:m.start()] + f"{m.group(1)}({x}:{x}:{x}) ({x}:{x}:{x})" + lines[i][m.end():]
    p = os.path.join(outd, f"{nm}", "gcd_hw.sdf")
    os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, "w").write("\n".join(out) + "\n")
    # rule scripts look for the routed JSON next to the SDF
    j = os.path.join(os.path.dirname(p), "gcd_hw_routed.json")
    if not os.path.exists(j):
        os.symlink(os.path.join(os.path.abspath(odir), "gcd_hw_routed.json"), j)
print("written", outd)
