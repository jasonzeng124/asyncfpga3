import sys, os, pickle
c_ = sys.argv[1]; PK = sys.argv[2]; sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
idx = {n: i for i, n in enumerate(nm)}
def E(e): return None if e is None else "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
P = pickle.load(open(PK, "rb")); M = P["MEMO"]
op = eid[(idx["SLICE_X30Y76.A6"], 2)]
for key, cl in M.items():
    if nm[key[0]] == "SLICE_X28Y67.A6" and cl.get("A") == op:
        print("claim", key[1:3], "A", E(cl["A"]), cl["a"], "ctx", [E(x) for x in key[-1]])
        for u, k in cl.get("cov") or []:
            w = M.get(k)
            if w: print("   pin", nm[u], w.get("kind"), "A", E(w.get("A")), w.get("a"), "Sep(A->open)", sepAny(w["A"], op)[0] if w.get("A") is not None else None)
        As = [M[k]["A"] for u, k in cl.get("cov") or [] if k in M and M[k].get("A") is not None]
        for x in As:
            print("   ", E(x), "->", [(E(y), sepAny(x, y)[0]) for y in As if y != x])
        break
