#!/usr/bin/env python3
"""Auditor's rule E (skew.py) recomputation with per-arc prjxray corner delays (own xrc.py model).

The rule's own structure is kept: graph = the route's SDF arcs after skew.py's false-arc and pruning steps
(imported from the research tree's verify/skew.py + tighten.py, the rule under test), the same select sites,
the same launch candidates (cand[:4] + link C nodes), the same level-unrolled walk (skew.walk).  Only the
arc WEIGHTS change: each interconnect arc gets the Elmore+site-pin+OUTMUX delay of the routed net to that
physical pin, each LUT cell arc the prjxray LUT6/LUT5 arc of the physical pin; arcs this model cannot
resolve (FF, CARRY4, MUXF7/8, constant nets) keep the SDF number in every corner ("fallback").

Per gate, min over launches, with the divergence credit taken from each walk's own table at the last common
node X of the two measured paths (shared prefix cancels):
  slow : req@SLOW_MIN - sel@SLOW_MAX     fast : req@FAST_MIN - sel@FAST_MAX
  slowG/fastG : 0.772*req - 1.155*sel on the same corner values (project band)
  mix  : req@FAST_MIN - sel@SLOW_MAX (fast-early / slow-late)   mixG: banded
  sdf  : the SDF numbers (should equal skew.py's raw margin)
    python3 rulee_x.py CELLS_DIR ROUTE_DIR TAG [gate-substring ...]"""
import sys, os, re, importlib
cells_dir, odir, tag = sys.argv[1:4]
only = sys.argv[4:]
sdf = [os.path.join(odir, f) for f in os.listdir(odir) if f.endswith(".sdf")][0]
sys.path.insert(0, "/home/user/asyncfpga3/audit/tc")
import xrc
R = xrc.Route(odir)
sys.argv = ["skew.py", sdf]
sys.path.insert(0, os.path.join(cells_dir, "verify"))
S = importlib.import_module("skew")
T = S.T
from collections import defaultdict

LO, HI = S.GUARD_LO, S.GUARD_HI
edges, celltype, n_io, n_ic = T.parse_sdf(S.SDF)
dead, jpath = T.false_arcs(edges)
for s in list(edges):
    edges[s] = [(d, w) for d, w in edges[s] if (s, d) not in dead]
sites = T.select_consumers(jpath)
stops = T.storage_nodes(edges)
side_arcs = T.fastfall_side_arcs(edges)

# --- re-weighting -----------------------------------------------------------------
nfb = [0, 0]
wt = {}


def weights(s, d, w):
    v = xrc.route_arc(R, s, d)   # LUT pins/arcs, MUXF7/F8 select nets, LUT->F7 hops, MUXF cell arcs
    if v is None:
        nfb[0] += 1
        return (float(w),) * 4, True
    nfb[1] += 1
    return tuple(v), False


for s, lst in edges.items():
    for d, w in lst:
        wt[(s, d)] = weights(s, d, w)
print(f"# {tag}: arcs resolved {nfb[1]}, fallback {nfb[0]}", file=sys.stderr)
if os.environ.get("XRC_FBSCALE"):
    # consistent-corner fallback: unresolved arcs scaled by the median model/SDF ratio of resolved arcs of
    # the same class (cell arc vs net), per corner, instead of keeping the SDF number in every corner
    import statistics
    cls = lambda s, d: "io" if (s.rsplit("/", 1)[0] == d.rsplit("/", 1)[0] and not T.is_output(s)) else "ic"
    rat = {"io": [[] for _ in range(4)], "ic": [[] for _ in range(4)]}
    for (s, d), (v, fb) in wt.items():
        w0 = next(w for dd, w in edges[s] if dd == d)
        if not fb and w0 > 0:
            for k in range(4):
                rat[cls(s, d)][k].append(v[k] / w0)
    med = {c: [statistics.median(x) for x in rat[c]] for c in rat}
    print(f"# fallback scaled by {med}", file=sys.stderr)
    for (s, d), (v, fb) in list(wt.items()):
        if fb:
            wt[(s, d)] = (tuple(v[0] * med[cls(s, d)][k] for k in range(4)), True)

VAR = {"sdf": None, "fmin": 0, "fmax": 1, "smin": 2, "smax": 3}


def edge_set(var, early):
    k = VAR[var]
    out = {}
    for s, lst in edges.items():
        out[s] = [(d, (w if k is None else wt[(s, d)][0][k])) for d, w in lst
                  if not (early and (s, d) in side_arcs)]
    return out


EW = {v: edge_set(v, True) for v in VAR}
LW = {v: edge_set(v, False) for v in VAR}
binc_w = {}
srcs_of = defaultdict(set)
for v in VAR:
    b = defaultdict(list)
    for s, lst in edges.items():
        for d, w in lst:
            b[d].append((s, w if VAR[v] is None else wt[(s, d)][0][VAR[v]]))
            srcs_of[d].add(s)
    binc_w[v] = b
binc0 = binc_w["sdf"]
feed = {(o, ip) for o in stops for ip, _ in binc0.get(o, ()) if o in srcs_of[ip]}


def back(pin):
    seen, cur = {pin: 0}, {pin}
    for k in range(S.K + 1):
        frontier, lvl = list(cur), set(cur)
        while frontier:
            nxt = []
            for pn in frontier:
                for s in srcs_of.get(pn, ()):
                    if (s, pn) in feed or s in seen:
                        continue
                    seen[s] = k; lvl.add(s)
                    if s not in stops:
                        nxt.append(s)
            frontier = nxt
        cur = set()
        for o in [x for x in lvl if x in stops]:
            for ip, _ in binc0.get(o, ()):
                if (o, ip) in feed or ip in seen:
                    continue
                seen[ip] = k + 1; cur.add(ip)
        if not cur:
            break
    return seen


def at(levels, pin):
    for k, tab in enumerate(levels):
        if pin in tab:
            return tab[pin], k
    return None


cache = {}


def fwd(launch, var, longest):
    key = (launch, var, longest)
    if key not in cache:
        cache[key] = S.walk(LW[var] if longest else EW[var], stops, binc_w[var], feed, launch, longest)
    return cache[key]


def margin(launch, rp, sp, rvar, svar):
    out_f, pred_f = fwd(launch, rvar, False)
    out_t, pred_t = fwd(launch, svar, True)
    e, l = at(out_f, rp), at(out_t, sp)
    if e is None or l is None:
        return None
    pr, ps = S.path_to(pred_f, e[1], rp), S.path_to(pred_t, l[1], sp)
    tcf = tct = 0.0
    if pr and ps:
        n = 0
        for a, b in zip(pr, ps):
            if a != b:
                break
            n += 1
        if n:
            xl, xn = pr[n - 1]
            tcf, tct = out_f[xl][xn], out_t[xl][xn]
    fb = 0
    for chain in (pr or [], ps or []):
        for (l1, a), (l2, b) in zip(chain, chain[1:]):
            if (a, b) in wt and wt[(a, b)][1]:
                fb += 1
    return dict(e=e[0], l=l[0], ek=e[1], lk=l[1], tcf=tcf, tct=tct, fb=fb,
                raw=(e[0] - tcf) - (l[0] - tct), g=LO * (e[0] - tcf) - HI * (l[0] - tct),
                raw0=e[0] - l[0], g0=LO * e[0] - HI * l[0])


checks = []
for kind, parent, reqs, sels in sites:
    by_cell = defaultdict(dict)
    for q in reqs:
        by_cell[T.pin_split(q)[0]]["req"] = q
    for q in sels:
        by_cell[T.pin_split(q)[0]]["sel"] = q
    for cell, dd in sorted(by_cell.items()):
        if "req" in dd and "sel" in dd:
            checks.append((kind, parent, cell, dd["req"], dd["sel"]))

COMBOS = {"sdf": ("sdf", "sdf"), "fast": ("fmin", "fmax"), "slow": ("smin", "smax"), "mix": ("fmin", "smax")}
print("seed\tgate\tsdf_raw\tsdf_g\tfast\tslow\tfastG\tslowG\tmix\tmixG\tfastG0\tslowG0\tmixG0\tfb_arcs\tworst_launch_slowG")
for kind, parent, cell, rp, sp in checks:
    if only and not any(o in cell for o in only):
        continue
    br, bs = back(rp), back(sp)
    cand = sorted((bs[q], br[q], q) for q in set(br) & set(bs) if q in stops and not T.is_const(q))
    names = {q for _, _, q in cand}
    launches = [q for _, _, q in cand[:4]]
    if cand:
        k0 = cand[0][0]
        for ks, _, q in cand:
            if ks != k0:
                break
            m = S.RE_LATCH_OUT.match(T.pin_split(q)[0])
            cn = m and m.group(1) + ".ctl.u.u/O6"
            if cn and cn in names and cn not in launches:
                launches.append(cn)
    res = {}
    for name, (rv, sv) in COMBOS.items():
        best = None
        for la in launches:
            r = margin(la, rp, sp, rv, sv)
            if r is None:
                continue
            r["launch"] = la
            if best is None or r["g"] < best["g"]:
                best = r
            res.setdefault(name + "_all", []).append(r)
        res[name] = best
    if res.get("sdf") is None:
        print(f"{tag}\t{cell}\tNO LAUNCH"); continue
    mn = lambda nm, f: round(min(r[f] for r in res[nm + "_all"]))
    print("\t".join(str(x) for x in (tag, cell, mn("sdf", "raw0"), round(res["sdf"]["g"]), mn("fast", "raw"), mn("slow", "raw"),
                                      mn("fast", "g"), mn("slow", "g"), mn("mix", "raw"), mn("mix", "g"),
                                      mn("fast", "g0"), mn("slow", "g0"), mn("mix", "g0"),
                                      max(r["fb"] for nm in COMBOS for r in res[nm + "_all"]),
                                      res["slow"]["launch"].replace("urig.udut.", ""))))
    sys.stdout.flush()
