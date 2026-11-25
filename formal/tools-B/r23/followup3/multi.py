"""multi-anchor check for the bank latches' U' at their openings: for every leaf cover claim w in the D-claim tree
(latch/exact/env claims, or comb claims anchored before the open), with the longest hi path P from w's node to Q's D
pin: need  w.A + w.a + hi(P) <= open + elo(Q,en)   i.e.  margin = elo + Sep(w.A -> open) - w.a - hi(P) >= 0.
usage: UPREL=1 multi.py c PKL"""
import sys, os, pickle, collections
c_ = sys.argv[1]; PK = sys.argv[2]; sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
idx = {n: i for i, n in enumerate(nm)}
def E(e): return None if e is None else "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
P = pickle.load(open(PK, "rb")); M = P["MEMO"]
EN = idx["SLICE_X30Y76.A6"]
def pw(v, u):
    for p in g[v]["pins"]:
        if p["src"] == u and p["live"]: return p["win"][c]
worst = {}
def walk(key, hipath, op, out, depth=0):
    cl = M.get(key)
    if cl is None or depth > 40: return
    n = key[0]
    A = cl.get("A")
    if A is not None and A != op and (cl.get("kind") in ("latch", "ex", "env") or A != op):
        if cl.get("kind") != "comb" or el[A][0] != EN:
            d = 0 if A == op else sepAny(A, op)[0]
            m = (d - cl["a"] - hipath) if d > -INF else None
            out.append((nm[n], cl.get("kind"), E(A), cl["a"], hipath, d if d > -INF else None, m))
            if cl.get("kind") != "comb": return
    if cl.get("kind") in ("comb", "comb-chain"):
        for u, k in cl.get("cov") or []:
            if k is None: continue
            walk(k, hipath + pw(n, u)[1], op, out, depth + 1)
R = collections.defaultdict(list)
for tr in P["TRUNC"]:
    if tr["kind"] != "H->U'" or not nm[tr["Q"]].startswith(("SLICE_X30Y7", "SLICE_X31Y7")): continue
    Q = tr["Q"]; op = tr["c2"]["A"]
    if el[op][0] != EN: continue
    elo = tr["c1"]["b"]
    out = []
    for (u, k, B, b) in tr["c2"].get("pins", []):
        walk(k, pw(Q, u)[1], op, out)
    ms = [x[-1] for x in out]
    worst[(nm[Q], E(op))] = (elo, min([m for m in ms if m is not None], default=None), sum(1 for m in ms if m is None), len(out), sorted(out, key=lambda x: (x[-1] is not None, x[-1] if x[-1] is not None else 0))[:2])
nok = sum(1 for v in worst.values() if v[2] == 0 and v[1] is not None and v[1] + v[0] >= 0)
print("[c=%s] bank H->U' truncations at X30Y76.A6 openings: %d; multi-anchor closes (all leaves margin+elo >= 0): %d" % (c_, len(worst), nok))
for k, v in sorted(worst.items()):
    print("  %s open %s elo %d  min(leaf margin)+elo %s  leaves without Sep %d of %d  worst %s" % (k[0], k[1], v[0], (v[1] + v[0]) if v[1] is not None else None, v[2], v[3], v[4][:1]))
