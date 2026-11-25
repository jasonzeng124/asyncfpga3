import sys, pickle, collections
c = sys.argv[1]; vname = sys.argv[2]; bname = sys.argv[3]
sys.argv = ["ao.py", c, "0", "--prevanc"]
src = open("/tmp/claude-0/race/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
idn = {n: i for i, n in enumerate(nm)}
v = idn[vname]; b = idn[bname]
def show(v):
    print("node", nm[v], "init %x" % g[v]["init"], "class", "CTRL" if v in C["CTRL"] else "EXC")
    for j, p in enumerate(g[v]["pins"]):
        if p["live"]: print("   pin%d %-18s win %s ev %s" % (j, nm[p["src"]], p["win"][int(c)], ev.get(p["src"], "data/const")))
    for k in range(len(ev[v])):
        e = eid[(v, k)]
        print("   event %d t=%d alts %s" % (k, ev[v][k], [[(nm[el[p][0]], el[p][1], el[p][2]) for p in a] for a in alts[e]]))
show(v)
for p in g[v]["pins"]:
    if p["live"] and p["src"] in EX and p["src"] != b and p["src"] != v: show(p["src"])
