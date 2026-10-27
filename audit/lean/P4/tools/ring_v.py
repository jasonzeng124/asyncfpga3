import json, sys, re, heapq
d = json.load(open(sys.argv[1]))
top = d["modules"]["bdc_gcd"]
names = {}
for n, nn in top["netnames"].items():
    for b in nn["bits"]:
        names.setdefault(b, []).append(n)
cells = top["cells"]
drv, rd = {}, {}
for cn, c in cells.items():
    pd = c.get("port_directions", {})
    for p, bits in c["connections"].items():
        dirn = pd.get(p)
        for b in bits:
            if isinstance(b, str): continue
            (drv if dirn == "output" else rd).setdefault(b, []).append((cn, p))
# forward edges: through nets named *_req
edges = {cn: set() for cn in cells}
nreq = 0
for b, ds in drv.items():
    if not any(n.endswith("_req") for n in names.get(b, [])): continue
    nreq += 1
    for (a, _) in ds:
        for (c, _) in rd.get(b, []):
            edges[a].add(c)
w = {}
for cn, c in cells.items():
    t = c["type"]
    if "bd_pipe" in t:
        w[cn] = int(d["modules"][t]["parameter_default_values"]["N"], 2)
    elif "bd_link" in t: w[cn] = 1
    else: w[cn] = 0
print("cells", len(cells), "req nets", nreq, "edges", sum(len(v) for v in edges.values()), "link stages", sum(w.values()))
types = {}
for cn, c in cells.items(): types[c["type"]] = types.get(c["type"], 0) + 1
# min cycle weight through each node (node weights, count weight of entering nodes)
best = None; arg = None
for s in cells:
    dist = {s: 0}; pq = [(0, s)]
    while pq:
        dd, u = heapq.heappop(pq)
        if dd > dist[u]: continue
        for v in edges[u]:
            nd = dd + w[v]
            if v == s:
                if best is None or nd < best: best, arg = nd, s
                continue
            if nd < dist.get(v, 1 << 60):
                dist[v] = nd; heapq.heappush(pq, (nd, v))
print("min stages on any cycle of the req graph:", best, "via", arg)
# count cycles existence: SCC sizes
