#!/usr/bin/env python3
# usage: python3 traceA.py SEED   (needs build/tree_SEED from route.sh)
# C-10h trace: tighten rule A with guard 0 (min raw over pairs) vs the raw of the worst-guarded pair.
import sys, pathlib
sys.path.insert(0, "/home/user/asyncfpga3/formal/tools/tcheck")
seed = sys.argv[1]
H = pathlib.Path("/home/user/asyncfpga3/formal/tools/tcheck")
cells = H / f"build/tree_{seed}/cells"
sys.path.insert(0, str(cells / "verify")); sys.path.insert(0, str(cells / "hw"))
sys.argv = [sys.argv[0]]
import tighten as T
from collections import defaultdict
sdf = cells / "build/hw/gcd_hw/gcd_hw.sdf"
edges, _ct, _a, _b = T.parse_sdf(sdf)
dead, _ = T.false_arcs(edges, sdf)
for s in list(edges):
    edges[s] = [(d, w) for d, w in edges[s] if (s, d) not in dead]
stops = T.storage_nodes(edges)
for prefix in ("dhk", "invhk"):
    for s in list(edges):
        i = T.pin_split(s)[0]
        if i == prefix or i.startswith(prefix + "."):
            edges[s] = []
back = defaultdict(set)
for s, l in edges.items():
    for d, _ in l:
        back[d].add(s)
timing = T.Timing(edges, stops)
chains = T.find_chains(edges)
for parent, head, tail, links in T.request_sites(edges, back, chains):
    if "control_merge" not in parent:
        continue
    downstream = T.reaches(edges, tail, stops)
    up, work = {head}, [head]
    while work:
        x = work.pop()
        for s in back.get(x, ()):
            if s not in up:
                up.add(s)
                if s not in stops:
                    work.append(s)
    upstream = {p for p in up if T.is_output(p) and p in edges}
    own = set(links)
    peers = sorted({p for p in edges if T.is_output(p) and T.pin_split(p)[0].startswith(parent + ".")
                    and T.pin_split(p)[0] not in own and p not in downstream and p not in upstream})
    if not peers:
        continue
    ps = T.cell_boundary(edges, back, stops, parent)
    ul = T.upstream_bd_links(ps)
    region = (parent,) + ul
    srcs = T.cell_boundary(edges, back, stops, region)
    confine = region if ul else parent
    g = T.check(timing, srcs, peers, tail, T.req_guard, confine=confine)
    z = T.check(timing, srcs, peers, tail, lambda p, t: 0, confine=confine)
    if g and z:
        print(f"{parent}\tguarded-pair raw {g[0] + g[1]}\tmin raw {z[0]}\tdiff {z[0] - g[0] - g[1]}")
