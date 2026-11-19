import json, os, pathlib, sys
repo, sdf, parent = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), sys.argv[3]
sys.path.insert(0, str(repo / "cells" / "verify")); sys.argv = [sys.argv[0], str(sdf)]
import skew, tighten as T
edges, back, stops = T.routed_graph(sdf)
celltype = T.parse_sdf(sdf)[1]
top = list(json.load(open(sdf.with_name(sdf.stem + "_routed.json")))["modules"].values())[0]
jc = top["cells"]; b2n = {}
for n, d in top["netnames"].items():
    for b in d["bits"]: b2n.setdefault(b, n)
site = [s for s in T.request_sites(edges, back, T.find_chains(edges)) if s[0] == parent][0]
tail = site[2]
seen, work, par = {tail}, [tail], {tail: None}
while work:
    p = work.pop()
    for d, w in edges.get(p, ()):
        if d in seen: continue
        seen.add(d); par[d] = p
        if d in stops: continue
        if not T.is_output(d) and not edges.get(d):
            ct = celltype.get(T.pin_split(d)[0])
            inst = T.pin_split(d)[0]; c = jc.get(inst, {})
            conns = {k: [b2n.get(b, b) for b in v] for k, v in c.get("connections", {}).items()}
            print("SINK", ct, d, "Q=", conns.get("Q"), "CK=", conns.get("CK"), "CE=", conns.get("CE"), "SR=", conns.get("SR"))
            continue
        if not T.is_output(d) and celltype.get(T.pin_split(d)[0]) == "SLICE_FFX":
            print("FF-IN-WITH-ARC", d, edges.get(d))
        work.append(d)
print("stops reached:", sorted(s for s in seen if s in stops))
