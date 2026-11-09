import sys, os
os.environ["UPREL"] = "1"
c_ = sys.argv[1]; sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
idx = {n: i for i, n in enumerate(nm)}
def E(e): n, k, t = el[e]; return "%s(%d)@%d" % (nm[n], k, t)
def evat(n, t):
    i = idx[n]; ks = [k for (nn, k) in [(i, k) for k in range(60)] if (i, k) in eid and el[eid[(i, k)]][2] == t]
    return eid[(i, ks[0])]
pairs = {"0": [("SLICE_X30Y76.A6", 403827, "SLICE_X36Y71.A6", 407710)], "1": []}
import pickle
M0 = pickle.load(open("/tmp/claude-0/bsub1/tocc/model.pkl", "rb"))
for a, ta, b, tb in pairs[c_]:
    A = evat(a, ta); B = evat(b, tb)
    s, _ = sepAny(A, B); print(E(A), "->", E(B), "leqP", leqP(A, B), "rev", leqP(B, A), "Sep", s)
    m = np.minimum(VCP[A], VCP[B]); cands = []
    for x in np.nonzero(m)[0]:
        e0 = eid[(xs[x], int(m[x]) - 1)]; cands.append((tm[e0], e0))
    cands.sort(reverse=True)
    for _, e0 in cands[:5]:
        U = up_from(e0, int(tm[A])); print("   e0", E(e0), "Sep(e0->B)", sep23(e0, B), "Up(e0->A)", U.get(A))
q = idx["SLICE_X37Y71.B5"]; G = M0["gates"][q]
print("X37Y71.B5 pins", [(nm[p["src"]], p["live"], p["win"][int(c_)]) for p in G["pins"]])
for n in ["SLICE_X34Y77.D5", "SLICE_X37Y71.B5", "SLICE_X36Y71.A6"]:
    print(n, [x for x in hist[idx[n]][1] if 380000 < x < 420000] if idx[n] in hist else None)
