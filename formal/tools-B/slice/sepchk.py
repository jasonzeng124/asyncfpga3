#!/usr/bin/env python3
"""[slice diag] Sep (ao.py sepAny/sep23, forms ii/iii/iv) and causal order between two events in one slice dir.
usage: sepchk.py dir NODE1 k1 NODE2 k2   (Sep from (NODE1,k1) to (NODE2,k2))"""
import sys, io, contextlib
D = "/tmp/claude-0/slice/" + sys.argv[1]; a, ka, b, kb = sys.argv[2], int(sys.argv[3]), sys.argv[4], int(sys.argv[5])
sys.argv = ["ao.py", "0", "0"]; g_ = {}
src = open(D + "/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
with contextlib.redirect_stdout(io.StringIO()): exec(src, g_)
nm = g_["nm"]; eid = g_["eid"]; ix = {n: i for i, n in enumerate(nm)}
A = eid[(ix[a], ka)]; B = eid[(ix[b], kb)]; el = g_["el"]
VC = g_["vclock"]({}); xi = g_["xi"]
print(D, "%s(%d)@%d -> %s(%d)@%d" % (a, ka, el[A][2], b, kb, el[B][2]))
print("  causally below (VC):", VC[B, xi[ix[a]]] > ka, " sep23:", g_["sep23"](A, B), " sepAny:", g_["sepAny"](A, B)[0])
