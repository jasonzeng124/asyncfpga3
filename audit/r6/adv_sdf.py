#!/usr/bin/env python3
"""Adversarial SDF for BQ#3 rule A ushrsi1 (audit r6).
   adv_sdf.py XRAY_SDF ARCS_TSV ROUTED_JSON OUTDIR [cell]
Writes OUTDIR/fmax/gcd_hw.sdf (every arc's first column = prjxray FAST_MAX) and
OUTDIR/adv/gcd_hw.sdf (FAST_MIN everywhere except the arcs that lie ONLY on the
cell's rule-A data side -- upstream controller -> upstream latch -> cell logic -> peers --
which get FAST_MAX).  Request-side and shared arcs stay FAST_MIN.  Also prints rule A's
req/peak/lag for the cell on fmin, fmax and adv using tighten.py's own functions."""
import sys, os, re, pathlib, importlib.util, shutil
from collections import defaultdict
xsdf, arcs, rjson, outd = sys.argv[1:5]
CELL = sys.argv[5] if len(sys.argv) > 5 else "urig.udut.ushrsi1"
TL = "/home/user/wt-r6/cells/verify/tighten.py"
un = lambda s: s.replace("\\", "")
# --- FAST_MAX / FAST_MIN per arc
fmax, fmin = {}, {}
for ln in open(arcs):
    p = ln.rstrip("\n").split("\t")
    if p[0] not in ("IC", "IO"): continue
    fmin[(p[1], p[2])] = int(p[4]); fmax[(p[1], p[2])] = int(p[5])
RI = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RO = re.compile(r"^(\s*\(IOPATH\s+(\S+)\s+(\S+)\s+)\((-?\d+):(-?\d+):(-?\d+)\)\s*\((-?\d+):(-?\d+):(-?\d+)\)(.*)$")
RC = re.compile(r"^(\s*\(INTERCONNECT\s+(\S+)\s+(\S+)\s+)\((-?\d+):(-?\d+):(-?\d+)\)\s*\((-?\d+):(-?\d+):(-?\d+)\)(.*)$")
lines = open(xsdf).read().splitlines()
keyed = []   # (line idx, key, prefix, rest)
inst = None
for i, l in enumerate(lines):
    m = RI.search(l)
    if m: inst = un(m.group(1)); continue
    m = RC.match(l)
    if m: keyed.append((i, (un(m.group(2)), un(m.group(3))), m)); continue
    m = RO.match(l)
    if m and inst is not None:
        keyed.append((i, (f"{inst}/{un(m.group(2))}", f"{inst}/{un(m.group(3))}"), m))
miss = sum(1 for _, k, _ in keyed if k not in fmax)
print(f"sdf arcs {len(keyed)}, without arcs.tsv FAST_MAX {miss}")
def write(path, sel):
    out = list(lines)
    for i, k, m in keyed:
        if sel(k) and k in fmax:
            v = fmax[k]
            out[i] = f"{m.group(1)}({v}:{v}:{v}) ({v}:{v}:{v}){m.group(10)}"
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, "w").write("\n".join(out) + "\n")
    for f in ("gcd_hw_routed.json",):
        d = os.path.join(os.path.dirname(path), f)
        if not os.path.exists(d): os.symlink(rjson, d)
# --- tighten's graph and rule A sets for CELL
sys.argv = ["tighten.py", xsdf, "--osc", "dhk", "--osc", "invhk"]
spec = importlib.util.spec_from_file_location("tighten", TL); T = importlib.util.module_from_spec(spec)
spec.loader.exec_module(T)
def graph(sdfp):
    sdfp = pathlib.Path(sdfp)
    edges, _, _, _ = T.parse_sdf(sdfp)
    dead, _ = T.false_arcs(edges, sdfp)
    for s in list(edges): edges[s] = [(d, w) for d, w in edges[s] if (s, d) not in dead]
    stops = T.storage_nodes(edges)
    for pre in ("dhk", "invhk"):
        for s in list(edges):
            i = T.pin_split(s)[0]
            if i == pre or i.startswith(pre + "."): edges[s] = []
    back = defaultdict(set)
    for s, l in edges.items():
        for d, _ in l: back[d].add(s)
    return edges, back, stops
def ruleA(sdfp):
    edges, back, stops = graph(sdfp)
    timing = T.Timing(edges, stops); chains = T.find_chains(edges)
    for parent, head, tail, links in T.request_sites(edges, back, chains):
        if parent != CELL: continue
        downstream = T.reaches(edges, tail, stops)
        upstream = {p for p in edges if T.is_output(p) and head in T.reaches(edges, p, stops)}
        own = set(links)
        peers = sorted({p for p in edges if T.is_output(p) and T.pin_split(p)[0].startswith(parent + ".")
                        and T.pin_split(p)[0] not in own and p not in downstream and p not in upstream})
        psrcs = T.cell_boundary(edges, back, stops, parent)
        ul = T.upstream_bd_links(psrcs); region = (parent,) + ul
        srcs = T.cell_boundary(edges, back, stops, region)
        confine = region if ul else parent
        res = T.check(timing, srcs, peers, tail, T.req_guard, confine=confine); how = "common"
        if res is None:
            res = T.check_bundled(timing, srcs, peers, tail, T.req_guard, confine=confine); how = "bundled"
        lag = T.upstream_data_lag(timing, back, confine, ul, srcs) if how == "bundled" else 0
        margin, g, te, tl, pin, s = res[:6]
        return dict(edges=edges, back=back, stops=stops, timing=timing, peers=peers, srcs=srcs, confine=confine,
                    tail=tail, ul=ul, how=how, req=te, peak=tl + lag, lag=lag, guard=g, raw=te - tl - lag,
                    margin=margin - lag, pin=pin, esrc=s, lsrc=res[6] if len(res) > 6 else s)
fmaxp = os.path.join(outd, "fmax/gcd_hw.sdf"); write(fmaxp, lambda k: True)
A0 = ruleA(xsdf); A1 = ruleA(fmaxp)
for nm, A in (("FAST_MIN", A0), ("FAST_MAX", A1)):
    print(f"{nm}: {A['how']} req {A['req']} peak {A['peak']} (lag {A['lag']}) raw {A['raw']} guard {A['guard']} "
          f"tighten-margin {A['margin']}  late pin {A['pin']}  early src {A['esrc']}  late src {A['lsrc']}")
print(f"interval (req FAST_MIN - peak FAST_MAX): {A0['req'] - A1['peak']}")
# --- cones (structure only)
E, back, stops, conf = A0["edges"], A0["back"], A0["stops"], A0["confine"]
pref = (conf,) if isinstance(conf, str) else conf
inside = lambda p: any(T.pin_split(p)[0] == x or T.pin_split(p)[0].startswith(x + ".") for x in pref)
def fwd(starts):
    seen = set(starts); work = list(starts)
    while work:
        u = work.pop()
        if u in stops and u not in starts: continue
        for v, _ in E.get(u, ()):
            if inside(v) and v not in seen: seen.add(v); work.append(v)
    return seen
def bwd(targets):
    seen = set(targets); work = list(targets)
    while work:
        v = work.pop()
        for u in back.get(v, ()):
            if u in seen or not (inside(u) or u in A0["srcs"]): continue
            seen.add(u)
            if u not in stops: work.append(u)
    return seen
def arcset(F, B):
    return {(u, v) for u in F for v, _ in E.get(u, ()) if v in F and v in B and u in B and (u not in stops or u in F0starts)}
srcs = set(A0["srcs"])
F0starts = srcs
F = fwd(srcs)
# data side: srcs -> peers, plus the upstream controller -> upstream latch lag paths
latch = {p for p in srcs if any(T.pin_split(p)[0].startswith(l + ".") and ".lat." in T.pin_split(p)[0] for l in A0["ul"])}
Bd = bwd(set(A0["peers"])) | bwd(latch)
data = arcset(F, Bd)
Br = bwd({A0["tail"]})
req = arcset(F, Br)
only = data - req
print(f"data-side arcs {len(data)}, request-side arcs {len(req)}, shared {len(data & req)}, data-only -> FAST_MAX {len(only)}")
advp = os.path.join(outd, "adv/gcd_hw.sdf"); write(advp, lambda k: k in only)
A2 = ruleA(advp)
print(f"ADV: req {A2['req']} peak {A2['peak']} (lag {A2['lag']}) raw {A2['raw']} tighten-margin {A2['margin']}")
with open(os.path.join(outd, "adv_arcs.txt"), "w") as f:
    for u, v in sorted(only): f.write(f"{u}\t{v}\t{fmin.get((u,v))}\t{fmax.get((u,v))}\n")
