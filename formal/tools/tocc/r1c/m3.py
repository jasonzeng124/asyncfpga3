import sys
c_ = sys.argv[1]
sys.argv = ["datal.py", c_]
src = open("/tmp/claude-0/r1c/datal.py").read(); src = src[:src.index("# ---------------- guards")]
exec(src)
idn = {n_: i for i, n_ in enumerate(nm)}
TGT = eid[(idn['SLICE_X16Y18.A6'], 1)]
LOG = []
orig = claim
def claim(n, t, t2=None):
    r = orig(n, t, t2)
    if isinstance(r, dict) and r.get("B") == TGT: LOG.append((nm[n], t, t2, r.get("kind"), r.get("b")))
    return r
# rebind for recursion: functions reference global 'claim'
globals()["claim"] = claim
v = idn['SLICE_X10Y28.A6']; z = idn['SLICE_X11Y31.B6']
st = (idn['SLICE_X10Y26.B6'], 0); en_ = (idn['SLICE_X10Y26.B6'], 1)
def mid_(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
ts = ev[st[0]][0] + mid_(v, st[0]); te = ev[st[0]][1] + mid_(v, st[0])
CTX.append(tuple(sorted([eid[st], eid[en_]])))
r = claim(z, ts - mid_(v, z), te - mid_(v, z))
print("z claim B:", r["B"] is not None and (nm[el[r["B"]][0]], el[r["B"]][1]), "b", r["b"])
for x in LOG[:40]: print("  ", x)
print("truncations:", {k: v_ for k, v_ in stats.items() if "trunc" in k})
