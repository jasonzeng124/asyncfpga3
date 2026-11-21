import sys
c_ = sys.argv[1]
sys.argv = ["datal.py", c_]
src = open("/tmp/claude-0/arbh/datal.py").read(); src = src[:src.index("# ---------------- guards")]
exec(src)
idn = {n_: i for i, n_ in enumerate(nm)}
a = eid[(idn['SLICE_X17Y18.B6'], 0)]; b = eid[(idn['SLICE_X16Y18.A6'], 1)]; cl = eid[(idn['SLICE_X10Y53.D6'], 1)]
print("tm order 17Y18(0) < 16Y18(1):", tm[a] < tm[b], " CP-below:", bool(leqP(a, b)))
print("Sep23 17Y18(0)->16Y18(1):", sep23(a, b), " form4:", form4(a, b))
print("Sep 16Y18(1) -> close 10Y53.D6(1):", sepAny(b, cl), " close->16Y18(1):", sepAny(cl, b))
# claim for 15Y19.B6 needed until the latch close read
z = idn['SLICE_X15Y19.B6']; t1 = 150000; t2 = ev[idn['SLICE_X10Y53.D6']][1] + 315 - 736
OBL.clear()
r = claim(z, t1, t2)
print("claim 15Y19.B6 over [%d,%d]:" % (t1, t2), {k: ((nm[el[v][0]], el[v][1]) if k in "AB" and v is not None else v) for k, v in r.items() if k in ("A","a","B","b","kind","bad")})
for o in OBL: print("  obl", o[0][:50], o[1], o[2] if isinstance(o[2], str) else o[2][0])
