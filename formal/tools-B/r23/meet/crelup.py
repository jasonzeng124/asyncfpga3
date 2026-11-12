import sys, os, threading
sys.setrecursionlimit(200000); threading.stack_size(1024 * 1024 * 1024)
def main():
    c_ = sys.argv[1]; sys.argv = ["ao.py", c_, "0"]
    g_ = {"__name__": "x"}
    src = open("/tmp/claude-0/bsub1/tocc/ao_orig.py").read(); src = src[:src.index("# ---------------- rounds")]
    exec(src, g_)
    exec(open("/home/user/asyncfpga3/formal/tools/tocc/r1b/relup.py").read().split("# ---------------- emission")[0], g_)
    nm, eid, el = g_["nm"], g_["eid"], g_["el"]; idx = {n: i for i, n in enumerate(nm)}
    E = lambda e: "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
    es = eid[(idx["SLICE_X42Y97.B6"], 2)]; A = eid[(idx["SLICE_X22Y87.A6"], 0)]; p = eid[(idx["SLICE_X32Y65.C6"], 2)]
    D = g_["RELD"]
    print("C relup (REL=%s RELD=%d RELK=%d RELTRY=%d): Up(e*->A) =" % (g_["REL"], D, g_["RELK"], g_["RELTRY"]), g_["up_get"](es, A, D),
          "| rel bound for p:", g_["_rel"](p, es, D), "| Sep23(e*->Cr) =", g_["sep23"](es, eid[(idx["SLICE_X24Y77.A6"], 2)]), flush=True)
th = threading.Thread(target=main); th.start(); th.join()
