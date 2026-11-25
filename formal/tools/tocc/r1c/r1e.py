import sys, collections, pickle, json, os
c_ = sys.argv[1]; sys.argv = ["datal.py", c_]
src = open("/tmp/claude-0/r1c/datal.py").read(); src = src[:src.index("# ---------------- guards")]
exec(src)
an = open("/tmp/claude-0/r1c/r1an.py").read(); exec(an[an.index("ARBQ = {}"):an.index("roots = collections.defaultdict(list)")])
d_ = open("/tmp/claude-0/r1c/r1d.py").read(); exec(d_[d_.index("def first_block"):d_.index("res = []")])
idn = {x: i for i, x in enumerate(nm)}
pend1 = eid[(bs["pend_ack"], 1)]; req1 = eid[(bs["req"], 1)]
for Xn, Yn in [(("SLICE_X39Y47.D6", 1), ("SLICE_X30Y76.A6", 2)), (("SLICE_X39Y47.D6", 1), ("SLICE_X36Y69.A6", 4))]:
    X = eid[(idn[Xn[0]], Xn[1])]; Y = eid[(idn[Yn[0]], Yn[1])]
    print("X", en(X), "Y", en(Y), "| pend_ack fall below X:", bool(leqP(pend1, X)), "below Y:", bool(leqP(pend1, Y)), "| req fall below X/Y:", bool(leqP(req1, X)), bool(leqP(req1, Y)))
    com = [e for e in range(NE) if leqP(e, X) and leqP(e, Y)]
    com.sort(key=lambda e: -tm[e])
    # sample candidates across the whole history
    idx = sorted(set(list(range(0, len(com), max(1, len(com) // 40))) + [com.index(req1)]))
    for i in idx:
        e0 = com[i]; U = up_from(e0, int(tm[X])); s = sep23(e0, Y)
        if X in U: print("   e0=%s: Sep(e0->Y)=%s Up(e0->X)=%d margin %d" % (en(e0), s, U[X], s - U[X]))
        else: print("   e0=%s: Sep(e0->Y)=%s Up none: %s" % (en(e0), s, first_block(e0, X, U)))
