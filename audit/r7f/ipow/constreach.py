"""Auditor: on a routed SDF, does a tie-off driver reach any rule-A request
tail (which would let check() pair through the constant and skip the more
pessimistic check_bundled)?  Uses tighten's parser/graph only."""
import importlib.util, sys, os
from collections import defaultdict
tpath, sdf = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
sys.argv = [tpath, sdf]; os.chdir(os.path.dirname(os.path.dirname(tpath)))
spec = importlib.util.spec_from_file_location("tighten", tpath)
t = importlib.util.module_from_spec(spec); spec.loader.exec_module(t)
edges, *_ = t.parse_sdf(t.SDF)
dead, _ = t.false_arcs(edges)
for s in list(edges): edges[s] = [(d, w) for d, w in edges[s] if (s, d) not in dead]
back = defaultdict(set)
for s, l in edges.items():
    for d, _ in l: back[d].add(s)
stops = t.storage_nodes(edges); tim = t.Timing(edges, stops)
chains = t.find_chains(edges); sites = t.request_sites(edges, back, chains)
consts = [p for p in edges if t.is_const(p)]
print("const driver pins:", consts, "fanout arcs:", {c: len(edges[c]) for c in consts})
nreach = 0
for parent, head, tail, links in sites:
    for c in consts:
        ub = t.upstream_bd_links(t.cell_boundary(edges, back, stops, parent))
        region = (parent,) + ub
        for conf in (None, parent, region if ub else parent):
            if tail in tim.early(c, conf):
                nreach += 1; print("REACHES tail", parent, c, "confine", conf, tim.early(c, conf)[tail])
print("rule-A sites", len(sites), "const->tail reaches", nreach)
