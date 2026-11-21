import sys, os
os.environ["UPREL"] = "1"
c_ = sys.argv[1]; sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
import pickle
M0 = pickle.load(open("/tmp/claude-0/bsub1/tocc/model.pkl", "rb")); idx = {n: i for i, n in enumerate(nm)}
ARB = {idx[a["q"]]: a for a in M0["arbs"]}
def E(e): n, k, t = el[e]; return "%s(%d)@%d%s" % (nm[n], k, t, "[ARB]" if n in ARB else "")
def ev(n, k): return eid[(idx[n], k)]
def lastev(n, t):
    ks = [k for k in range(len(ev_[idx[n]])) if ev_[idx[n]][k] <= t]; return ks[-1] if ks else None
ev_ = ev  # placeholder
EV = {n: [x for x in (hist[n][1] if n in hist else []) if x > t0] for n in EX}
for Q, en in (("SLICE_X36Y63.B6", "SLICE_X36Y63"), ("SLICE_X36Y68.B6", "SLICE_X36Y68")):
    pass
G = ev("SLICE_X38Y51.A6", 0); print("D-end", E(G))
for cl, E_ in ((("SLICE_X36Y63.A6", 1), ("SLICE_X36Y63.C6", 1)), (("SLICE_X36Y68.A6", 1), ("SLICE_X36Y68.C6", 1))):
    close = ev(*cl); Eg = ev(*E_)
    for nmx, A in (("close", close), ("guard E", Eg)):
        s, _ = sepAny(A, G)
        print("  %s %s -> D-end: leqP %s / reverse %s ; Sep %s" % (nmx, E(A), leqP(A, G), leqP(G, A), s))
    m = np.minimum(VCP[close], VCP[G]); cands = []
    for x in np.nonzero(m)[0]:
        e0 = eid[(xs[x], int(m[x]) - 1)]; cands.append((tm[e0], e0))
    cands.sort(reverse=True)
    for _, e0 in cands[:6]:
        U = up_from(e0, int(tm[close])); print("     e0 %s  Sep(e0->Dend) %s  Up(e0->close) %s" % (E(e0), sep23(e0, G), U.get(close)))
# causes of the D-end event and arbiter events in its past
print("D-end alternatives:", [[E(p) for p in alt] for alt in alts[G]])
past = [e for e in range(NE) if leqP(e, G) and el[e][0] in ARB and el[e][2] > 300000]
print("ARB events below D-end (t>300ns):", [E(e) for e in past])
pastc = [e for e in range(NE) if leqP(e, ev("SLICE_X36Y63.A6", 1)) and el[e][0] in ARB and el[e][2] > 300000]
print("ARB events below close X36Y63.A6(1):", [E(e) for e in pastc])
a = ARB[idx["SLICE_X38Y51.B6"]]; print("arb0 ins", a["ins"])
print("X38Y51.A6 pins", [(nm[p["src"]], p["live"]) for p in g[idx["SLICE_X38Y51.A6"]]["pins"]])
for n in a["ins"] + ["SLICE_X38Y51.B6", "SLICE_X38Y51.A6", "SLICE_X38Y53.A6"]:
    if n in idx and idx[n] in EV: print("  ", n, [x for x in EV[idx[n]] if 300000 < x < 340000])
