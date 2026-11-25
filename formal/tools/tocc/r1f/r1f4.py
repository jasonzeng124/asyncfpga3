# hold margin of the two latches: for each exact source x reaching D through data gates, min lo path x -> latch D pin,
# first event of x causally after the close, Sep(close -> it); margin = Sep + lo_path - hi(en pin); kappa.
import sys, heapq
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/r1f/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[x]: x for x in range(len(nm))}
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
X = eid[(N["SLICE_X34Y92.A6"], 1)]
for qn in ("SLICE_X35Y91.B6", "SLICE_X34Y91.C5"):
    Q = N[qn]; fb, ens = C["LATCH"][Q]; pins = g[Q]["pins"]
    pe = [p for p, a in ens if nm[pins[p]["src"]] == "SLICE_X34Y92.A6"][0]; ehi = pins[pe]["win"][c][1]
    # Dijkstra backwards: dist[node] = min lo from node's output to Q's output (excluding Q's enable/fb pins)
    dist = {}; pq = []
    for j, p in enumerate(pins):
        if p["live"] and j not in fb and j != pe and p["src"] != Q: heapq.heappush(pq, (p["win"][c][0], p["src"]))
    res = []
    while pq:
        d, v = heapq.heappop(pq)
        if v in dist: continue
        dist[v] = d
        if v in EX:
            evs = [eid[(v, k)] for k in range(len(ev[v])) if leqP(X, eid[(v, k)])]
            if evs:
                y = evs[0]; sp = sep23(X, y); m = sp + d - ehi
                res.append((m, nm[v], s_(y), sp, d, ehi, (sp + d - ehi) / (sp + d + ehi)))
            else: res.append((None, nm[v], "no event after close", None, d, ehi, None))
            continue
        if v not in g or v in C["const"] or v in C["data_env"]: continue
        for p in g[v]["pins"]:
            if p["live"] and p["src"] != v: heapq.heappush(pq, (d + p["win"][c][0], p["src"]))
    res.sort(key=lambda r: (r[0] is None, r[0] if r[0] is not None else 0))
    print("== c=%s %s (hi en->Q %d)" % (cc, qn, ehi))
    for r in res[:6]: print("   margin %s  src %s ev %s Sep(close->ev) %s lo-path %s  flip kappa %s" % (r[0], r[1], r[2], r[3], r[4], ("%.3f" % r[6]) if r[6] is not None else None))
