#!/usr/bin/env python3
"""RT_FB (C-element / storage feedback race) recomputed with the auditor's prjxray model.
For each storage node o (tighten.storage_nodes) with feedback pin(s) f (o's own output routed back to o):
  data   = net o -> f  (late: corner MAX)
  request= shortest path o -> ... -> any OTHER input pin of o's cell, through any arc (Dijkstra, corner MIN),
           never passing through o's own cell.
  margin = request - data per corner; G = 0.772*request - 1.155*data; mix = req@FAST_MIN - data@SLOW_MAX.
    python3 rtfb_x.py CELLS_DIR ROUTE_DIR TAG [name-substring ...]"""
import sys, os, re, importlib, heapq
cells_dir, odir, tag = sys.argv[1:4]
only = sys.argv[4:]
sdf = [os.path.join(odir, f) for f in os.listdir(odir) if f.endswith(".sdf")][0]
sys.path.insert(0, "/home/user/asyncfpga3/audit/tc")
import xrc
R = xrc.Route(odir)
sys.argv = ["tighten.py", sdf]
sys.path.insert(0, os.path.join(cells_dir, "verify"))
T = importlib.import_module("tighten")
import pathlib
edges, *_ = T.parse_sdf(pathlib.Path(sdf))
dead, jpath = T.false_arcs(edges)
for s in list(edges):
    edges[s] = [(d, w) for d, w in edges[s] if (s, d) not in dead]
stops = T.storage_nodes(edges)


def weights(s, d, w):
    cs, ps = s.rsplit("/", 1)
    cd, pd = d.rsplit("/", 1)
    v = None
    if cs == cd and not T.is_output(s):
        if cs in R.cells and re.fullmatch(r"A[1-6]", ps) and "LUT" in R.cells[cs]["type"]:
            v = R.lut_arc(cs, ps, pd)
    elif cd in R.cells and cs in R.cells and re.fullmatch(r"A[1-6]", pd) and "LUT" in R.cells[cd]["type"]:
        b = R.cells[cd]["connections"][pd][0]
        if R.driver.get(b) == (cs, ps):
            n, sk = R.sink_of_cellpin(cd, pd)
            if sk is not None and n.ok:
                v = sk["d"]
    return (tuple(v), False) if v is not None else ((float(w),) * 4, True)


W = {(s, d): weights(s, d, w) for s, lst in edges.items() for d, w in lst}
SDFW = {(s, d): w for s, lst in edges.items() for d, w in lst}


def dij(src, cell, k):
    """shortest arrival from src to every input pin of `cell` (other than via the cell itself)"""
    dist = {src: 0.0}
    pq = [(0.0, src)]
    best = {}
    while pq:
        t, u = heapq.heappop(pq)
        if t > dist.get(u, 1e18):
            continue
        for d, w in edges.get(u, ()):
            x = SDFW[(u, d)] if k is None else W[(u, d)][0][k]
            cd = d.rsplit("/", 1)[0]
            if cd == cell:
                if not T.is_output(d) and u != src:
                    best[d] = min(best.get(d, 1e18), t + x)
                elif not T.is_output(d) and u == src:
                    pass  # the feedback arc itself
                continue
            if t + x < dist.get(d, 1e18):
                dist[d] = t + x
                heapq.heappush(pq, (t + x, d))
    return best


print("seed\tnode\tfb_pin\tfb_sdf\tfb_prjx(fmin,fmax,smin,smax)\treq_pin_sdf\treq_sdf\treq_fmin\treq_smin\tsdf\tfast\tslow\tfastG\tslowG\tmix\tfb_fallback")
for o in sorted(stops):
    cell = o.rsplit("/", 1)[0]
    if only and not any(x in cell for x in only):
        continue
    fbs = [(d, w) for d, w in edges.get(o, ()) if d.rsplit("/", 1)[0] == cell]
    if not fbs:
        continue
    req = {k: dij(o, cell, k) for k in (None, 0, 2)}
    for f, wsdf in fbs:
        (fv, fb) = W[(o, f)]
        r = {k: min((v for p, v in req[k].items() if p != f), default=None) for k in req}
        if r[None] is None:
            continue
        rp = min((p for p in req[None] if p != f), key=lambda p: req[None][p])
        row = (tag, cell, f.rsplit("/", 1)[1], wsdf, "/".join(str(round(x)) for x in fv), rp.rsplit("/", 1)[1], round(r[None]),
               round(r[0]), round(r[2]), round(r[None] - wsdf), round(r[0] - fv[1]), round(r[2] - fv[3]),
               round(0.772 * r[0] - 1.155 * fv[1]), round(0.772 * r[2] - 1.155 * fv[3]), round(r[0] - fv[3]), int(fb))
        print("\t".join(map(str, row)))
