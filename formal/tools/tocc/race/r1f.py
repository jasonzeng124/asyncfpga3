"""Path-skew adversary for the R1 pairs (UNTRUSTED). usage: r1f.py c
For each re-open event Y of an R1 pair (r1c_c<c>.pkl, positive gap only), with Xs = all deadlines paired with Y:
NX = gates having an event below some X but not below Y; NY = gates with an event below Y but not below any X.
Every input pin of a gate in NX - NY is set to its window hi, of NY - NX to lo; the rest stay at mid.
Writes adv/skew_c<c>_<i>.json (ADV for simenv.py) and adv/skew_c<c>.pkl (the pairs to check)."""
import sys, collections, pickle, json
c_ = sys.argv[1]; sys.argv = ["datal.py", c_]
src = open("/tmp/claude-0/race/datal.py").read(); src = src[:src.index("# ---------------- guards")]
exec(src)
idn = {x: i for i, x in enumerate(nm)}
D = pickle.load(open("/tmp/claude-0/race/r1c_c%s.pkl" % c_, "rb"))["OUT"]
byY = collections.defaultdict(list)
for d in D:
    if d["kind"] == "reopen" and d["tY"] > d["tX"]: byY[d["Y"]].append(d["X"])
out = []
for i, (Yn, Xs) in enumerate(sorted(byY.items(), key=lambda kv: -len(kv[1]))):
    Y = eid[(idn[Yn[0]], Yn[1])]; XE = [eid[(idn[x[0]], x[1])] for x in Xs]
    below = lambda e, T: leqP(e, T) or e == T
    NX = set(); NY = set()
    for e in range(NE):
        v = el[e][0]
        if v not in g: continue
        bY = below(e, Y); bX = any(below(e, X) for X in XE)
        if bX and not bY: NX.add(v)
        if bY and not bX: NY.add(v)
    slow = [[nm[v], nm[p["src"]]] for v in NX - NY for p in g[v]["pins"]]
    fast = [[nm[v], nm[p["src"]]] for v in NY - NX for p in g[v]["pins"]]
    json.dump(dict(slowpins=slow, fastpins=fast), open("/tmp/claude-0/race/adv/skew_c%s_%d.json" % (c_, i), "w"))
    print("Y=%s(%d)@%d with %d deadlines: slow gates %d, fast gates %d, conflicting %d" % (Yn[0], Yn[1], et[Y], len(Xs), len(NX - NY), len(NY - NX), len(NX & NY)))
    out.append(dict(i=i, Y=Yn, Xs=Xs))
pickle.dump(out, open("/tmp/claude-0/race/adv/skew_c%s.pkl" % c_, "wb"))
