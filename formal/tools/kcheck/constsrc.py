#!/usr/bin/env python3
"""Probe C-10n diagnostic (UNTRUSTED): does a project rule-A row take its data peak from a
CONSTANT driver?  tighten.cell_boundary() does not skip $PACKER_GND_DRV/$PACKER_VCC_DRV, so
check_bundled() starts the data side at the tie-off driver too, and a long tie-off route (3-5 ns
on these routes) becomes the "latest" data.  A constant never switches: that path is false.
    python3 constsrc.py ROUTE_DIR CELLS_DIR       (ROUTE_DIR holds soak.sdf)
Prints, per rule-A site, the project's peak and margin with tighten's srcs and with the
constant drivers removed (same tighten code otherwise; nothing in cells/ is modified)."""
import pathlib, sys
from collections import defaultdict
route, cells = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
sys.path.insert(0, str(cells / "verify")); sys.argv = [sys.argv[0]]
import tighten as T  # noqa: E402
sdf = route / "soak.sdf"
edges, _c, _a, _b = T.parse_sdf(sdf)
dead, _ = T.false_arcs(edges, sdf)
for s in list(edges):
    edges[s] = [(d, w) for d, w in edges[s] if (s, d) not in dead]
back = defaultdict(set)
for s, l in edges.items():
    for d, _ in l:
        back[d].add(s)
stops = T.storage_nodes(edges)
timing = T.Timing(edges, stops)
chains = T.find_chains(edges)
print("site\tpairing\tpeak(tighten srcs)\tmargin\tpeak(no const)\tmargin(no const)\tpeak src")
for parent, head, tail, links in T.request_sites(edges, back, chains):
    downstream = T.reaches(edges, tail, stops)
    upstream = {p for p in edges if T.is_output(p) and head in T.reaches(edges, p, stops)}
    own = set(links)
    peers = sorted({p for p in edges if T.is_output(p) and T.pin_split(p)[0].startswith(parent + ".")
                    and T.pin_split(p)[0] not in own and p not in downstream and p not in upstream})
    if not peers:
        continue
    up_links = T.upstream_bd_links(T.cell_boundary(edges, back, stops, parent))
    region = (parent,) + up_links
    srcs = T.cell_boundary(edges, back, stops, region)
    confine = region if up_links else parent
    pairing, f = "common", T.check
    res = T.check(timing, srcs, peers, tail, T.req_guard, confine=confine)
    if res is None:
        pairing, f = "bundled", T.check_bundled
        res = f(timing, srcs, peers, tail, T.req_guard, confine=confine)
    if res is None:
        continue
    nc = {s for s in srcs if not T.is_const(s)}
    r2 = f(timing, nc, peers, tail, T.req_guard, confine=confine)
    src = res[-1] if pairing == "bundled" else "-"
    print(f"{parent}\t{pairing}\t{res[3]}\t{res[0]}\t{r2[3] if r2 else '-'}\t{r2[0] if r2 else '-'}\t{src}")
