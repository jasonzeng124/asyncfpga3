import sys, pickle, collections
c = sys.argv[1]
sys.argv = ["ao.py", c, "0", "--prevanc"]
src = open("/tmp/claude-0/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
P = pickle.load(open("/tmp/claude-0/tocc/ao_c%s_prevanc.pkl" % c, "rb")); rf = P["rows_fail"]
idn = {n: i for i, n in enumerate(nm)}
cb = collections.Counter(r[4] for r in rf)
print("failing rows by b (top 8):", [(nm[b], n) for b, n in cb.most_common(8)])
print("failing rows a=v by b (top 5):", [(nm[b], n) for b, n in collections.Counter(r[4] for r in rf if r[1]==r[2]).most_common(5)])
for name in ("SLICE_X15Y92.B6", "SLICE_X0Y48.A6"):
    b = idn[name]
    rd = [v for v in g if any(p["src"] == b and p["live"] for p in g[v]["pins"])]
    kinds = collections.Counter("CTRL" if v in C["CTRL"] else ("EXC" if v in C["EXC"] else ("LATCH" if v in C["LATCH"] else "DATA")) for v in rd)
    gb = g[b]
    print("\n==", name, "class", "CTRL" if b in C["CTRL"] else ("EXC" if b in C["EXC"] else "?"), "k", gb["k"], "init %x" % gb["init"])
    print("  pins:", [(nm[p["src"]], p["live"], p["win"][int(c)][:2]) for p in gb["pins"]])
    print("  events:", ev[b])
    print("  readers %d by class %s" % (len(rd), dict(kinds)))
    his = sorted(dl[(v, b)][1] - dl[(v, b)][0] for v in rd if (v, b) in dl)
    print("  reader pin windows hi-lo: min %d median %d max %d; hi max %d" % (his[0], his[len(his)//2], his[-1], max(dl[(v,b)][1] for v in rd if (v,b) in dl)))
    print("  failing rows with this b: %d (a=v %d) at %d readers" % (cb[b], sum(1 for r in rf if r[4]==b and r[1]==r[2]), len(set(r[1] for r in rf if r[4]==b))))
    # what is it: trace sources back two levels
    for p in gb["pins"]:
        if p["live"] and p["src"] in g:
            s_ = p["src"]; print("   src", nm[s_], "class", "CTRL" if s_ in C["CTRL"] else ("EXC" if s_ in C["EXC"] else ("ENV" if s_ in envnode else "?")), "ev", ev.get(s_, [])[:6])
print("rst =", nm[bs["rst"]], "req =", nm[bs["req"]])
