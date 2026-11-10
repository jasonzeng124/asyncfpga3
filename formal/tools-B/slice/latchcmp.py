#!/usr/bin/env python3
"""[slice diag] latch claims of node N in each slice dir: phases (ph, A, a, B, b) with events named; truncations.
usage: latchcmp.py NODE dir..."""
import sys, pickle
N = sys.argv[1]
for D in sys.argv[2:]:
    D = "/tmp/claude-0/slice/" + D
    nm = pickle.load(open(D + "/model.pkl", "rb"))["names"]; ix = nm.index(N)
    sys.argv = ["ao.py", "0", "0"]; g_ = {}
    src = open(D + "/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
    import io, contextlib
    with contextlib.redirect_stdout(io.StringIO()): exec(src, g_)
    el = g_["el"]
    E = lambda e: None if e is None else "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
    P = pickle.load(open(D + "/dl_c0.pkl", "rb"))
    print("==", D)
    for k, cl in P["MEMO"].items():
        if not isinstance(cl, dict) or k[0] != ix or cl.get("kind") != "latch": continue
        print("  claim", k[1:3], "A", E(cl.get("A")), cl.get("a"), "B", E(cl.get("B")), cl.get("b"))
        for (ph, A, a, B, b, pins) in cl.get("chainw", []): print("     ", ph, E(A), a, E(B), b)
        if cl.get("trunc"): t = cl["trunc"]; print("     TRUNC", t["kind"], "c1.B", E(t["c1"]["B"]), t["c1"]["b"], "c2.A", E(t["c2"]["A"]), t["c2"]["a"], "margin", t["margin"])
