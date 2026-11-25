import sys
c_ = sys.argv[1]
sys.argv = ["datal.py", c_]
src = open("/tmp/claude-0/tocc/datal.py").read(); src = src[:src.index("# ---------------- guards")]
exec(src)
idn = {n_: i for i, n_ in enumerate(nm)}
E = lambda n, k: eid[(idn[n], k)]
a = E('SLICE_X17Y18.B6', 0); b = E('SLICE_X16Y18.A6', 1); cl = E('SLICE_X10Y53.D6', 1); b2 = E('SLICE_X17Y18.B6', 1)
p17 = pwin(idn['SLICE_X15Y19.B6'], idn['SLICE_X17Y18.B6']); p16 = pwin(idn['SLICE_X15Y19.B6'], idn['SLICE_X16Y18.A6'])
s1 = sepAny(a, b)[0]
print("[c=%s] OR hand-over at SLICE_X15Y19.B6: Sep(17Y18.B6(0) -> 16Y18.A6(1)) = %s; need hi(15Y19,17Y18) - lo(15Y19,16Y18) = %d - %d; margin %s" % (c_, s1, p17[1], p16[0], s1 - (p17[1] - p16[0])))
# latch 11Y53.A6 hold: its D (15Y19.B6) must stay valid until its close (10Y53.D6(1)) is read: D claim now ends at 17Y18.B6(1)
pD = pwin(idn['SLICE_X11Y53.A6'], idn['SLICE_X15Y19.B6']); pE = pwin(idn['SLICE_X11Y53.A6'], idn['SLICE_X10Y53.D6'])
s2 = sepAny(cl, b2)[0]
print("  latch SLICE_X11Y53.A6 hold: Sep(close 10Y53.D6(1) -> 17Y18.B6(1)) = %s; need hi(en) - lo(17Y18 -> 15Y19) - lo(D pin) = %d - %d - %d; margin %s" % (s2, pE[1], p17[0], pD[0], s2 + p17[0] + pD[0] - pE[1]))
print("  path of the Sep (form ii/iii only):", sep23(cl, b2))
