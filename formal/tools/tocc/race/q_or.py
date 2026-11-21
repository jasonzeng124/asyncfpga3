import sys
c_ = sys.argv[1]; sys.argv = ["datal.py", c_]
src = open("/tmp/claude-0/race/datal.py").read(); src = src[:src.index("# ---------------- guards")]
exec(src)
idn = {x: i for i, x in enumerate(nm)}
z = idn["SLICE_X39Y53.B6"]; a = idn["SLICE_X38Y53.A6"]; b = idn["SLICE_X38Y51.A6"]
for k in range(len(ev[a])):
    for j in range(len(ev[b])):
        A = eid[(a, k)]; B = eid[(b, j)]
        if leqP(A, B) and valat(a, ev[a][k]) and not valat(b, ev[b][j]):
            print("rise %s(%d)@%d -> fall %s(%d)@%d: Sep23 %s; need > hi(z,a) - lo(z,b) = %d" % (nm[a], k, ev[a][k], nm[b], j, ev[b][j], sep23(A, B), pwin(z, a)[1] - pwin(z, b)[0]))
