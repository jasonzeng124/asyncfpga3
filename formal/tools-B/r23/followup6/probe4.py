import sys, os
os.environ["UPREL"] = "1"
c_ = sys.argv[1]; sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
idx = {n: i for i, n in enumerate(nm)}
def E(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
def evnear(n, t):
    i = idx[n]; return min((eid[(i, k)] for k in range(len(ev[i]))), key=lambda e: abs(el[e][2] - t))
tA = {"0": 374823, "1": None}[c_]
a = evnear("SLICE_X22Y87.A6", 374823 if c_ == "0" else 862155); b = evnear("SLICE_X27Y80.A6", 377006 if c_ == "0" else 870000)
print(E(a), "vs", E(b), "leqP a<=b", leqP(a, b), "b<=a", leqP(b, a), "Sep(a->b)", sepAny(a, b)[0], "Sep(b->a)", sepAny(b, a)[0])
m = np.minimum(VCP[a], VCP[b]); cands = []
for x in np.nonzero(m)[0]:
    e0 = eid[(xs[x], int(m[x]) - 1)]; cands.append((tm[e0], e0))
cands.sort(reverse=True)
for _, e0 in cands[:4]:
    U = up_from(e0, int(max(tm[a], tm[b])))
    print("  e0", E(e0), "Up(e0->a)", U.get(a), "Sep(e0->b)", sep23(e0, b))
