import pickle, sys, collections
import numpy as np
sys.path.insert(0, "/tmp/claude-0/r1c")
from classify import load
C = load(); nm = C["names"]
suf = sys.argv[1] if len(sys.argv) > 1 else ""
P = [pickle.load(open("/tmp/claude-0/r1c/ao_c%d_prevanc_cyc_causeanc_dcp%s.pkl" % (c, suf), "rb")) for c in (0, 1)]
ev_ = [[(n, k) for (n, k, t) in p["el"]] for p in P]
print("events: c0 %d, c1 %d, identical (node, index) lists: %s" % (len(ev_[0]), len(ev_[1]), ev_[0] == ev_[1]))
def altkey(p, e): return sorted(tuple(sorted((p["el"][q][0], p["el"][q][1]) for q in a)) for a in p["alts"][e])
if ev_[0] == ev_[1]:
    da = [e for e in range(len(ev_[0])) if altkey(P[0], e) != altkey(P[1], e)]
    print("events with different alternatives: %d" % len(da))
    for e in da[:8]:
        n, k = ev_[0][e]; print("   %s(%d): c0 %s | c1 %s" % (nm[n], k, [[(nm[a], b) for a, b in x] for x in altkey(P[0], e)], [[(nm[a], b) for a, b in x] for x in altkey(P[1], e)]))
    def rtset(p): return set(((p["el"][U][0], p["el"][U][1]), (p["el"][W][0], p["el"][W][1])) for W, us in p["rt"].items() for U in us)
    r0, r1 = rtset(P[0]), rtset(P[1])
    print("RT edges: c0 %d, c1 %d, common %d, only c0 %d, only c1 %d" % (len(r0), len(r1), len(r0 & r1), len(r0 - r1), len(r1 - r0)))
    for x in list(r0 - r1)[:4] + list(r1 - r0)[:4]: print("   ", "c0-only" if x in r0 else "c1-only", nm[x[0][0]], x[0][1], "->", nm[x[1][0]], x[1][1])
    vd = np.argwhere(P[0]["VC"] != P[1]["VC"])
    print("CF order bound (VC) entries differing: %d of %d" % (len(vd), P[0]["VC"].size))
    print("tm (topological stamps) identical: %s" % bool(np.array_equal(P[0]["tm"], P[1]["tm"])))
