import sys, pickle, collections
c = sys.argv[1]; SUF = sys.argv[2] if len(sys.argv) > 2 else ""
sys.argv = ["ao.py", c, "0"] + (["--prevanc"] if SUF == "_prevanc" else [])
src = open("/tmp/claude-0/race/ao.py").read()
src = src[:src.index("# ---------------- rounds")]
exec(src)
P = pickle.load(open("/tmp/claude-0/race/ao_c%s%s.pkl" % (c, SUF), "rb")); rt = P["rt"]
VC = vclock(rt)
weak_nodes = set(r[1] for r in P["rows_fail"])
fl = collections.Counter(); nodes = set()
for v in sorted(EX):
    Lv = lambda a, k, b: int(VC[eid[(a, k)], xi[b]])
    D, nv_, out = check(v, Lv)
    for kind, nn in out:
        if not kind.endswith("~"): fl[kind] += 1; nodes.add(v)
fin = [f for f in P["fails"]]
print("c=%s: failures with UNWEAKENED L (CF order, all TO rows ignored): %s at %d nodes" % (c, dict(fl), len(nodes)))
print("  final failures at readers with a lowered L entry: %d of %d (nodes %d of %d)" % (
    sum(1 for f in fin if f[0] in weak_nodes), len(fin), len(set(f[0] for f in fin) & weak_nodes), len(set(f[0] for f in fin))))
print("  final failing nodes: CTRL storage %d, comb %d, env %d" % (
    sum(1 for v in set(f[0] for f in fin) if v in C["CTRL"]), sum(1 for v in set(f[0] for f in fin) if v in C["EXC"]),
    sum(1 for v in set(f[0] for f in fin) if v in envnode)))
