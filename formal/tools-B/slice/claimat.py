#!/usr/bin/env python3
"""[slice diag] claims of node N whose key interval contains time T (run time of that slice): A,a,B,b, covers (pin src,
cover kind/claim key), bind. usage: claimat.py NODE dir T"""
import sys, pickle, io, contextlib
N, D, T = sys.argv[1], "/tmp/claude-0/slice/" + sys.argv[2], int(sys.argv[3])
nm = pickle.load(open(D + "/model.pkl", "rb"))["names"]; ix = nm.index(N)
sys.argv = ["ao.py", "0", "0"]; g_ = {}
src = open(D + "/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
with contextlib.redirect_stdout(io.StringIO()): exec(src, g_)
el = g_["el"]; E = lambda e: None if e is None else "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
P = pickle.load(open(D + "/dl_c0.pkl", "rb"))
for k, cl in P["MEMO"].items():
    if not isinstance(cl, dict) or k[0] != ix: continue
    if not ((len(k) > 3 and isinstance(k[2], int) and k[2] > 100 and k[1] <= T <= k[2]) or abs(k[1] - T) <= 3000): continue
    print("claim key", k[1:3], "kind", cl.get("kind"), "A", E(cl.get("A")), cl.get("a"), "B", E(cl.get("B")), cl.get("b"), "bind", str(cl.get("bind"))[:80])
    for c in cl.get("cov", []) or []:
        print("    cov", nm[c[0]], "claim", (nm[c[1][0]],) + tuple(c[1][1:3]) if isinstance(c[1], tuple) else c[1])
