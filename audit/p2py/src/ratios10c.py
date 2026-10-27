#!/usr/bin/env python3
"""Audit: recompute C-10c ring-0 ratios from per-ring prjx.json, with sensitivity."""
import json, statistics as st, sys
B = "/home/user/asyncfpga3/audit/p2py/f10c/formal/tools/prjxdelay/build/"
S = ("sdefault", "s1", "s2", "s3")
many = [dict(r, route="many_" + s) for s in S for r in json.load(open(B + f"ro_many_top_{s}/prjx.json"))["rings"]]
top = [dict(r, route="top_" + s) for s in S for r in json.load(open(B + f"ro_top_{s}/prjx.json"))["rings"]]
MEAS, SDF0, SIL = 6293, 4674, 0.989
# recompute the prepatch period from stages (lut + prepatch_ic) and current from (lut + sdf_ic)
for r in many + top:
    pp = 2 * sum(x["sdf_lut"] + x["prepatch_ic"] for x in r["stages"])
    cc = 2 * sum(x["sdf_lut"] + x["sdf_ic"] for x in r["stages"])
    assert abs(pp - r["sdf_prepatch_period_ps"]) <= 1 and abs(cc - r["sdf_period_ps"]) <= 1, r["ring"]
print("stage sums consistent with periods: ok (%d rings)" % len(many + top))
cur = lambda r: r["sdf_period_ps"]; pre = lambda r: r["sdf_prepatch_period_ps"]
prj = lambda i: (lambda r: r["prjx_period_ps"][i])
def scale(f, pop=many): return SIL / st.median(f(r) / pre(r) for r in pop)
sc, sp = scale(cur), scale(prj(3))
print(f"scales: current {sc:.4f}  prjx slow_max {sp:.4f}  prepatch {SIL}")
r7 = [r for r in many + top if r["links"] == 7]
def report(tag, near, sc=sc, sp=sp, spre=SIL):
    if not near: print(f"{tag:46s} n=0"); return
    a = MEAS / st.median(spre * pre(r) for r in near)
    b = MEAS / st.median(sc * cur(r) for r in near)
    c = MEAS / st.median(sp * prj(3)(r) for r in near)
    lo = MEAS / max(sp * prj(3)(r) for r in near); hi = MEAS / min(sp * prj(3)(r) for r in near)
    print(f"{tag:46s} n={len(near):3d}  pre {a:.3f}  cur {b:.3f}  prjx {c:.3f}  (prjx per-ring range {lo:.3f}..{hi:.3f})")
for tol in (0, 300, 700, 1000, 1500, 99999):
    report(f"tol {tol} ps around 4674 (many+top)", [r for r in r7 if abs(pre(r) - SDF0) <= tol])
report("tol 700, ro_many only", [r for r in many if r["links"] == 7 and abs(pre(r) - SDF0) <= 700])
report("ro_top ring0 re-routes only (same design)", [r for r in top if r["links"] == 7])
print("ro_top ring0 prepatch SDFs:", [pre(r) for r in top if r["links"] == 7], "current:", [cur(r) for r in top if r["links"] == 7])
# unscaled (raw) predictions
near = [r for r in r7 if abs(pre(r) - SDF0) <= 700]
report("tol 700, UNSCALED (s=1 for all)", near, 1, 1, 1)
# scale fitted on 7-link population only
s7c = SIL / st.median(cur(r) / pre(r) for r in many if r["links"] == 7)
s7p = SIL / st.median(prj(3)(r) / pre(r) for r in many if r["links"] == 7)
report("tol 700, scales from 7-link pop (sil 0.989)", near, s7c, s7p)
s7c2 = 1.176 / st.median(cur(r) / pre(r) for r in many if r["links"] == 7)
s7p2 = 1.176 / st.median(prj(3)(r) / pre(r) for r in many if r["links"] == 7)
report("tol 700, scales to 7-link silicon med 1.176", near, s7c2, s7p2, 1.176)
for i, nm in ((0, "fast_min"), (1, "fast_max"), (2, "slow_min")):
    s_i = scale(prj(i))
    v = MEAS / st.median(s_i * prj(i)(r) for r in near)
    print(f"tol 700, prjx corner {nm:8s} scaled: {v:.3f}")
# the hard-coded 0.989: README pooled median
print("distinct prepatch values in near set:", sorted({pre(r) for r in near}), "current values:", sorted({cur(r) for r in near}))
