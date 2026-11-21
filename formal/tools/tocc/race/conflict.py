import sys, pickle, collections
sys.path.insert(0, "/tmp/claude-0/race")
from cert import build
from timing import Tm
for c in (0, 1):
    K = build(c); tm = Tm(K); eid = K["eid"]; ev = K["ev"]
    M = pickle.load(open("min_c%d.pkl" % c, "rb")); A = pickle.load(open("an_c%d_all.pkl" % c, "rb"))
    glob = 0; other = collections.Counter()
    for (v, kind, n, best) in M["kept"]:
        if kind == "X": continue
        D = A["res"][v]["D"]; hit = False
        for iu, u in enumerate(D):
            if n[iu] >= len(ev[u]): continue
            for iw, w in enumerate(D):
                if iw != iu and n[iw] > 0 and tm.leq(eid[(u, n[iu])], eid[(w, n[iw] - 1)]): hit = True
        if hit: glob += 1
        else: other[kind] += 1
    print("c=%d remaining after weakening: violate the ORIGINAL causal order (lost only by global weakening) %d; others %s" % (c, glob, dict(other)))
