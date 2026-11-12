#!/usr/bin/env python3
"""[slice diag] datal_t's own sep()/upq() (CRELUP config) between two events, plus the JoinAnc best margin terms.
usage (env as the builder): dsep.py dir NODE1 k1 NODE2 k2  -> sep((1)->(2)), upq((1)->(2)), upq((2)->(1))"""
import sys, os, threading
D = "/tmp/claude-0/slice/" + sys.argv[1]; args = sys.argv[2:]
sys.setrecursionlimit(400000); threading.stack_size(1024 * 1024 * 1024)
def main():
    src = open(D + "/datal_t.py").read(); src = src[:src.index("\ndef claim(")]
    g_ = {"__name__": "x"}; sys.argv = ["datal_t.py", "0"]
    import io, contextlib
    with contextlib.redirect_stdout(io.StringIO()): exec(compile(src, "datal_t.py", "exec"), g_)
    nm = g_["nm"]; eid = g_["eid"]; ix = {n: i for i, n in enumerate(nm)}; el = g_["el"]; tm = g_["tm"]
    A = eid[(ix[args[0]], int(args[1]))]; B = eid[(ix[args[2]], int(args[3]))]
    print(D, "A=%s(%s)@%d B=%s(%s)@%d" % (args[0], args[1], el[A][2], args[2], args[3], el[B][2]))
    print("  sep(A->B)", g_["sep"](A, B), " upq(A->B)", g_["upq"](A, B), " upq(B->A)", g_["upq"](B, A))
    m_ = g_["np"].minimum(g_["VCP"][A], g_["VCP"][B]); cs = []
    for x_ in g_["np"].nonzero(m_)[0]:
        a_ = eid[(g_["xs"][x_], int(m_[x_]) - 1)]; cs.append((tm[a_], a_))
    cs.sort(reverse=True)
    for _, a_ in cs[:10]:
        print("  common anc %s(%d)@%d: sep23(anc->B) %s  upq(anc->A) %s" % (nm[el[a_][0]], el[a_][1], el[a_][2], g_["sep23"](a_, B), g_["upq"](a_, A)))
th = threading.Thread(target=main); th.start(); th.join()
