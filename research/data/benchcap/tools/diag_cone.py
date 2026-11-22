#!/usr/bin/env python3
"""diag_cone.py REPO CORNER_SDF PARENT -- diagnosis only (not part of the flow).
For one operator: the A'j forward cone of its data (as corner_audit.rule_a_joined builds it), every sink the rule
calls odd (cell, pin, SDF celltype, the routed JSON's cell type and src attribute), the A' walk's path to its latest
peer, and for each odd FF: what clocks / enables it."""
import collections, json, os, pathlib, re, sys

repo, sdf, parent = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), sys.argv[3]
sys.path.insert(0, str(repo / "cells" / "verify"))
sys.argv = [sys.argv[0], str(sdf)]
os.environ.setdefault("BD_SKEW_AND_JOIN", "1")
import skew
import tighten as T

edges, back, stops = T.routed_graph(sdf)
celltype = T.parse_sdf(sdf)[1]
jpath = sdf.with_name(sdf.stem + "_routed.json")
top = list(json.load(open(jpath))["modules"].values())[0]
jcells, jnets = top["cells"], top["netnames"]
bit2net = {}
for n, d in jnets.items():
    for b in d["bits"]:
        bit2net.setdefault(b, n)
chains = T.find_chains(edges)
site = [s for s in T.request_sites(edges, back, chains) if s[0] == parent]
assert site, "no request site " + parent
_, head, tail, links = site[0]
print("site", parent, "head", head, "tail", tail, "links", len(links))
en_of = collections.defaultdict(set)
for c in stops:
    if not T.RE_BD_LATCH.search(T.pin_split(c)[0]):
        for dst, _ in T.latch_enables(edges, c):
            en_of[T.pin_split(dst)[0]].add(dst)
sel_req = {}
for kind, par, reqs, sels in T.select_consumers(jpath) or []:
    for q in sels:
        rq = [r for r in reqs if T.pin_split(r)[0] == T.pin_split(q)[0]]
        if rq:
            sel_req[q] = (rq, "%s %s" % (kind, par))
own = set(links)
inside = [p for p in edges if T.is_output(p) and T.pin_split(p)[0].startswith(parent + ".")]
downstream = T.reaches(edges, tail, stops)
upstream = {p for p in inside if head in T.reaches(edges, p, stops)}
peers = sorted(p for p in inside if T.pin_split(p)[0] not in own and p not in downstream and p not in upstream
               and not T.pin_split(p)[0].startswith(parent + ".ujoin."))
print("peers (%d):" % len(peers))
for p in peers:
    print("   ", p)
caps, odd, how = {}, set(), {}
seen, work = set(peers), list(peers)
par_of = {p: None for p in peers}
while work:
    p = work.pop()
    for d, _ in edges.get(p, ()):
        if d in seen:
            continue
        seen.add(d)
        par_of[d] = p
        if d in sel_req:
            caps[d] = "select"
            continue
        if not T.is_output(d) and not edges.get(d):
            if celltype.get(T.pin_split(d)[0]) not in ("SLICE_LUTX", "CARRY4", "SELMUX2_1"):
                odd.add(d); how[d] = "no arc, celltype %s" % celltype.get(T.pin_split(d)[0])
            continue
        if not T.is_output(d) and any(o in stops for o, _ in edges.get(d, ())):
            inst = T.pin_split(d)[0]
            if T.RE_BD_LATCH.search(inst) and en_of.get(inst) and d not in en_of[inst]:
                caps[d] = "latch"
            else:
                odd.add(d); how[d] = "storage input, not latch data / select"
            continue
        if d not in stops:
            work.append(d)


def chain_back(d):
    out = []
    while d is not None:
        out.append(d)
        d = par_of.get(d)
    return list(reversed(out))


def jinfo(inst):
    c = jcells.get(inst)
    if c is None:
        return "(not in JSON)"
    a = c.get("attributes", {})
    conns = {k: [bit2net.get(b, b) for b in v] for k, v in c.get("connections", {}).items()}
    return "type %s src %s conns %s" % (c.get("type"), a.get("src", "-"), json.dumps(conns)[:600])


print("\ncaptures (%d):" % len(caps))
for d, k in sorted(caps.items()):
    print("   ", k, d)
print("\nODD (%d):" % len(odd))
for d in sorted(odd):
    inst = T.pin_split(d)[0]
    print("  *", d, "--", how[d])
    print("      cone path:", " -> ".join(chain_back(d)))
    print("      json:", jinfo(inst))

# ---- the A' walk: from each upstream link C node, the request's earliest at the tail and every peer's latest
if len(sys.argv) > 1 and os.environ.get("DIAG_WALK", "1") == "1":
    sys.path.insert(0, str(repo / "research" / "tools"))
    import corner_audit as CA
    skew.AND_NODES.clear(); skew.AND_NODES.update(o for o in stops if skew.RE_CTREE_C.search(o))
    binc, srcs_of, feed = CA._incoming(edges, stops)
    side = T.fastfall_side_arcs(edges)
    early = CA._side_pruned(edges, side)
    bnd = T.cell_boundary(edges, back, stops, parent)
    ups = set(T.upstream_bd_links(bnd))
    ups |= {mm.group(1) for q in bnd for mm in [re.match(r"^(.*?)\.lat\.odd\.u$", T.pin_split(q)[0])] if mm}
    print("\nupstream links:", sorted(ups))
    for link in sorted(ups):
        for c in (link + ".ctl.u.u/O6", link + ".ctl.ub/O6"):
            if c not in stops:
                continue
            wf = skew.walk(early, stops, binc, feed, c, False)
            wt = skew.walk(edges, stops, binc, feed, c, True)
            def at(levels, pin, maxl=None):
                for k, tab in enumerate(levels[:maxl] if maxl else levels):
                    if pin in tab:
                        return tab[pin], k
            r = at(wf[0], tail)
            print("launch", c, "req at tail", r)
            if not r:
                continue
            for p in peers:
                v = at(wt[0][:r[1] + 2], p)
                if v is None:
                    continue
                pp = skew.path_to(wt[1], v[1], p) or []
                print("   peer %s data %s path: %s" % (p.split("/")[0].rsplit(".", 1)[-1], v,
                      " > ".join("%d:%s" % (l, n.replace("bridge_i.udut.", "")) for l, n in pp
                                 if T.is_output(n)) ))
