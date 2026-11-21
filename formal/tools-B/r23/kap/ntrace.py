"""net-level causal trace in a simadv dump (mid delays): for target flip, step to the input pin whose source flip
arrived latest (flip + mid arc delay <= t). Builds S/F arc lists for the race adversary.
usage: ntrace.py NET DUMP OUTPREFIX"""
import json, sys
from bisect import bisect_right
net = json.load(open(sys.argv[1])); N = net["nodes"]; G = net["gates"]; idx = {n: i for i, n in enumerate(N)}
drv = {g["out"]: gi for gi, g in enumerate(G)}
D = json.load(open(sys.argv[2])); H = {int(k): v for k, v in D["nodes"].items()}
R = D["args"]["R"]
def flips(n): return H[n][1] if n in H else []
def md(a): return (a["fmin"] + a["fmax"]) // 2
def trace(n, t, tmin):
    """returns list of arcs [(node_name, pin)] along the causal path and list of (node, t)"""
    arcs = []; nodes = [(N[n], t)]
    while n in drv and t > tmin:
        g = G[drv[n]]; best = None
        for j, (u, a) in enumerate(zip(g["ins"], g["arcs"])):
            if u == n: continue
            f = flips(u); i = bisect_right(f, t - md(a)) - 1
            if i >= 0 and f[i] >= tmin and (best is None or f[i] + md(a) > best[0]): best = (f[i] + md(a), u, j, f[i])
        if best is None: break
        arcs.append([N[n], best[2]]); n, t = best[1], best[3]; nodes.append((N[n], t))
    return arcs, nodes
def meet(pa, pb):
    """cut both paths at their first common node"""
    na = [x[0] for x in pa[1]]; nb = [x[0] for x in pb[1]]; sb = set(nb)
    for i, x in enumerate(na):
        if x in sb:
            j = nb.index(x); return pa[0][:i], pb[0][:j], x
    return pa[0], pb[0], None
z = idx["SLICE_X22Y81.B5"]; dat = idx["SLICE_X22Y87.D5"]; sel = idx["SLICE_X27Y80.B6"]; Q = idx["SLICE_X25Y76.B5"]; en = idx["SLICE_X24Y77.A6"]
S = []; F = []; FE = []; info = []
zf = flips(z)
for ts in [x for x in flips(sel) if x > R]:
    td = [x for x in flips(dat) if x <= ts]
    if not td: continue
    td = td[-1]
    if any(td - 1 <= x <= ts + 3000 for x in zf): continue      # output changed: not a hand-over
    pa = trace(dat, td, td - 60000); pb = trace(sel, ts, ts - 60000)
    a_, b_, m = meet(pa, pb)
    S += a_; F += b_
    te = [x for x in flips(en) if x > ts]
    if te:
        pe = trace(en, te[0], te[0] - 60000); e_, _, me = meet(pe, pb)
        FE += e_
    info.append(dict(sel_flip=ts, data_flip=td, meet=m, nS=len(a_), nF=len(b_)))
# last arcs into z: data pin slow, select pin fast; Q's enable pin fast for the variant
gz = G[drv[z]]
for j, u in enumerate(gz["ins"]):
    uu = u
    while uu in drv and G[drv[uu]]["k"] == 1 and G[drv[uu]]["init"] == 2: uu = G[drv[uu]]["ins"][0]
print(json.dumps(info))
def pinarcs(v, src):
    g = G[drv[v]]; out = []
    for j, u in enumerate(g["ins"]):
        hops = []; uu = u
        while uu in drv and G[drv[uu]]["k"] == 1 and G[drv[uu]]["init"] == 2: hops.append(uu); uu = G[drv[uu]]["ins"][0]
        if uu == src: out += [[N[v], j]] + [N[h] for h in hops]
    return out
S += pinarcs(z, dat); F += pinarcs(z, sel); FE += pinarcs(Q, en)
def uniq(L): 
    s = []; [s.append(x) for x in L if x not in s]; return s
S = uniq(S); F = [x for x in uniq(F) if x not in S]; FE = [x for x in uniq(FE) if x not in S]
json.dump({"S": S, "F": F}, open(sys.argv[3] + "_race.json", "w"))
json.dump({"S": S, "F": uniq(F + FE)}, open(sys.argv[3] + "_race_en.json", "w"))
print("S arcs", len(S), "F arcs", len(F), "F+enable arcs", len(uniq(F + FE)))
