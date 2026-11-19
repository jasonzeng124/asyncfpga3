"""diag_selrace.py REPO SDF MUX CTL_C -- bdc_muxnN's select race at its decode LUTs (sel[k] = ctl_req & (s == k)):
from the select link's C node, the latest arrival of s (through its latch) at each decode LUT vs the earliest of ctl_req.
Diagnosis only (no rule measures this race today)."""
import os, pathlib, sys
repo, sdf, mux, ctl = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), sys.argv[3], sys.argv[4]
sys.path.insert(0, str(repo / "cells" / "verify")); sys.path.insert(0, str(repo / "research" / "tools"))
sys.argv = [sys.argv[0], str(sdf)]
import skew, tighten as T, corner_audit as CA
edges, back, stops = T.routed_graph(sdf)
skew.AND_NODES.clear(); skew.AND_NODES.update(o for o in stops if skew.RE_CTREE_C.search(o))
binc, srcs_of, feed = CA._incoming(edges, stops)
early = CA._side_pruned(edges, T.fastfall_side_arcs(edges))
lo = skew.walk(edges, stops, binc, feed, ctl, True)[0]
ea = skew.walk(early, stops, binc, feed, ctl, False)[0]
def at(levels, pin, maxl=3):
    for k, tab in enumerate(levels[:maxl]):
        if pin in tab: return tab[pin], k
link = ctl.split(".ctl.")[0]
for p in sorted(edges):
    inst = T.pin_split(p)[0]
    if not (inst.startswith(mux + ".") and T.is_output(p)): continue
    outs = [d for d, _ in edges[p]]
    if not any(T.pin_split(d)[0].startswith(mux + ".uj") for d in outs): continue      # a decode LUT: feeds a join
    pins = sorted({s for s in back if T.pin_split(s)[0] == inst and not T.is_output(s)})
    req, sel = [], []
    for ip in pins:
        src = sorted(back.get(ip, ()))
        kind = "req" if any(".rdly." in s or ".ctl." in s for s in src) else ("s" if any(link + ".lat." in s for s in src) else "other")
        e, l = at(ea, ip), at(lo, ip)
        (req if kind == "req" else sel if kind == "s" else []).append((ip, e, l))
    t_req = min((e[0] for _, e, _ in req if e), default=None)
    t_s = max((l[0] for _, _, l in sel if l), default=None)
    print("%s: ctl_req earliest %s ps, s latest %s ps -> s leads ctl_req by %s ps  (req pins %s; s pins %s)" % (
        inst.split(".udut.")[1], t_req, t_s, (t_req - t_s) if t_req is not None and t_s is not None else "-",
        [(T.pin_split(i)[1], e) for i, e, _ in req], [(T.pin_split(i)[1], l) for i, _, l in sel]))
