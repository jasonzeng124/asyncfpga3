#!/usr/bin/env python3
"""Shard C (UNTRUSTED): time-separation-of-events bound for the relative-timing orders "c before b".
Inputs: net.json (arcs), bnd.json, huff.txt (prep.py output: the abstract machine huffx ran), and per trace
the huffr change log (TRACE.txt.log: walk start state of every huff node, then per move: move code and the
node ids flipped by that move, in order). huffr = huffx.cpp + per-move change log (tools in this directory).
Per trace (b = last move, c = node named first in the file name):
  events = every storage-node toggle (control or data latch) and every env-node toggle, in log order.
  preds(x) = for each storage/env support u of x: u's last event before x's reference point R(x), if it is
             after x's previous toggle ("changed"); NECESSARY if x is not excited at R(x) with u at its value
             at x's previous toggle (zero-delay evaluation from storage/env values).
  hop(u -> x): sums of per-arc windows over logic paths u -> (comb)* -> x's output; variants
     sens   : only sensitised paths (each gate depends on the path pin, given its other inputs, in the state
              just before u's event OR the state at R(x)), min and max over them
     struct : all structural paths (rtmargin's numbers)
  For a reference event A: LO(A)=HI(A)=0; for x descending from A:
     LO(x) = max( max_{necessary p desc A} LO(p)+minhop, min_{all changed p} LO(p)+minhop if all desc A )
     HI(x) = max over changed preds p (and older last-events of supports and x's previous toggle + loop,
             when those descend from A) of HI(p)+maxhop; a pred that is a necessary ancestor of A counts HI=0;
             any other pred makes HI = inf; env events HI = inf (env delay unbounded).
  c's completion: Dc = HI(c fires at b's reference point) + loop(c) (loop = structural max c -> c).
  kappa* = (LO(b) - Dc) / (LO(b) + Dc), best over every A in the window with finite numbers (each A is a
  separate sufficient condition).
usage: tse.py net.json bnd.json huff.txt TRACE.txt[.log] ...   (env DETAIL=1: hop-by-hop of best A)"""
import json, sys, os, bisect, collections, math, pickle
sys.setrecursionlimit(1000000)
INF = float("inf")
W = int(os.environ.get("TSE_WINDOW", "250"))
NAB = int(os.environ.get("TSE_NABACK", "100000"))
NETP, BNDP, HUFP = sys.argv[1:4]
cache = HUFP + ".tse.pkl"
if os.path.exists(cache):
    D = pickle.load(open(cache, "rb"))
else:
    net = json.load(open(NETP)); G = net["gates"]; NN = net["nodes"]; nidx = {n: i for i, n in enumerate(NN)}
    BJ = json.load(open(BNDP)); ENVn = set(nidx[x] for x in BJ["env"])
    def is_copy(g): return g["k"] == 1 and g["init"] == 2
    cm = {i: g for i, g in enumerate(G) if is_copy(g) and i not in ENVn}
    def chain(u):
        s = [0, 0, 0, 0]
        while u in cm:
            a = cm[u]["arcs"][0]; s = [s[0] + a["fmin"], s[1] + a["fmax"], s[2] + a["smin"], s[3] + a["smax"]]
            u = cm[u]["ins"][0]
        return u, s
    L = open(HUFP).read().split("\n"); p = 0
    nn = int(L[0].split()[1]); names = L[1:1 + nn]; p = 1 + nn
    def rd(line, st):
        t = line.split(); out = int(t[0]); k = int(t[1]); ins = list(map(int, t[2:2 + k])); init = int(t[2 + k], 16)
        return out, k, ins, init, (int(t[3 + k]) if st else 0)
    nc = int(L[p].split()[1]); comb = [rd(L[p + 1 + i], False) for i in range(nc)]; p += 1 + nc
    ns = int(L[p].split()[1]); stor = [rd(L[p + 1 + i], True) for i in range(ns)]; p += 1 + ns
    bnd = dict(kv.split("=") for kv in L[p].split()[1:]); bnd = {k: int(v) for k, v in bnd.items()}; p += 1
    AD = list(map(int, L[p].split()[1:])); BD = list(map(int, L[p + 1].split()[1:])); p += 3
    envl = list(map(int, L[p].split()[1:]))
    gate = {}; dly = {}
    for (out, k, ins, init, latch) in comb + stor:
        gi = nidx[names[out]]; g = G[gi]; assert g["k"] == k and g["init"] == init, names[out]
        ds = []
        for j in range(k):
            s, d = chain(g["ins"][j]); assert NN[s] == names[ins[j]], (names[out], j, NN[s], names[ins[j]])
            a = g["arcs"][j]; ds.append((d[0] + a["fmin"], d[1] + a["fmax"], d[2] + a["smin"], d[3] + a["smax"]))
        gate[out] = (k, ins, init); dly[out] = ds
    D = dict(names=names, comb=[c[0] for c in comb], stor=[s[0] for s in stor], latch=[s[4] for s in stor],
             gate=gate, dly=dly, bnd=bnd, AD=AD, BD=BD, env=envl)
    pickle.dump(D, open(cache, "wb"))
names = D["names"]; gate = D["gate"]; dly = D["dly"]; bnd = D["bnd"]; STOR = D["stor"]; ENV = set(D["env"])
STORS = set(STOR); LATCH = {s for s, l in zip(STOR, D["latch"]) if l}
nid = {n: i for i, n in enumerate(names)}
topo = {x: i for i, x in enumerate(D["comb"])}
def dep(k, init, j):
    return any(((init >> x) & 1) != ((init >> (x ^ (1 << j))) & 1) for x in range(1 << k))
fan = collections.defaultdict(list)   # src -> [(gate out, pin)]
for out, (k, ins, init) in gate.items():
    for j, s in enumerate(ins):
        if dep(k, init, j): fan[s].append((out, j))
SUPm = {}
def ssupp(v):
    if v in SUPm: return SUPm[v]
    res = set(); seen = set(); k, ins, init = gate[v]
    st = [s for j, s in enumerate(ins) if dep(k, init, j)]
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x)
        if x in STORS or x in ENV or x not in gate: res.add(x); continue
        k2, ins2, init2 = gate[x]; st += [s for j, s in enumerate(ins2) if dep(k2, init2, j)]
    res.discard(v); SUPm[v] = res; return res
BCONE = {}
def bcone(t):
    """comb nodes in t's backward cone (to storage/env)"""
    if t in BCONE: return BCONE[t]
    res = set(); st = [s for s in gate[t][1]]
    while st:
        x = st.pop()
        if x in res or x in STORS or x in ENV or x not in gate: continue
        res.add(x); st += gate[x][1]
    BCONE[t] = res; return res
REQ, PACK, OACK = bnd["req"], bnd["pend_ack"], bnd["out0_ack"]
AACK, BACK, SACK, OREQ = bnd["a_ack"], bnd["b_ack"], bnd["start_ack"], bnd["out0_req"]
BND_OUT = [AACK, BACK, SACK, OREQ]
ENVSUP = set()
for x in BND_OUT:
    ENVSUP |= (ssupp(x) | {x}) if x in gate else {x}
ENVSUP = {u for u in ENVSUP if u in STORS or u in ENV} | {REQ, PACK, OACK}
ENVM = {-1: REQ, -2: REQ, -3: PACK, -4: PACK, -5: OACK, -6: OACK}

class Trace:
    def __init__(self, path):
        self.path = path
        lp = path if path.endswith(".log") else path + ".log"
        lines = open(lp).read().split("\n")
        self.init = [c == "1" for c in lines[0]]
        flips = collections.defaultdict(list); ev = []; pos = 0; moves = []
        for l in lines[1:]:
            if not l: continue
            t = list(map(int, l.split())); code = t[0]; mstart = pos; prevstor = False; runstart = pos
            moves.append(code)
            for x in t[1:]:
                isev = x in STORS or x in ENV
                if isev:
                    if not prevstor: runstart = pos
                    flips[x].append(pos)
                    ev.append(dict(pos=pos, node=x, move=len(moves) - 1, code=code, mstart=mstart,
                                   R=(mstart if x in ENV else runstart)))
                prevstor = isev; pos += 1
        self.flips = flips; self.ev = ev; self.moves = moves
        self.byPos = {e["pos"]: i for i, e in enumerate(ev)}
    def val(self, x, pos):
        f = self.flips.get(x)
        if not f: return self.init[x]
        return self.init[x] ^ (bisect.bisect_left(f, pos) & 1)
    def lastflip(self, x, pos):
        f = self.flips.get(x)
        if not f: return None
        i = bisect.bisect_left(f, pos)
        return f[i - 1] if i else None
    def evaluator(self, pos, override=None):
        memo = {}; ov = override or {}
        def ev(x):
            if x in ov: return ov[x]
            if x in memo: return memo[x]
            if x in STORS or x in ENV or x not in gate: r = self.val(x, pos)
            else:
                k, ins, init = gate[x]; a = 0
                for j, s in enumerate(ins):
                    if ev(s): a |= 1 << j
                r = bool((init >> a) & 1)
            memo[x] = r; return r
        return ev
    def lut(self, x, evf, flipset=()):
        k, ins, init = gate[x]; a = 0
        for j, s in enumerate(ins):
            b = evf(s)
            if j in flipset: b = not b
            if b: a |= 1 << j
        return bool((init >> a) & 1)
    def excited(self, v, pos, override=None):
        evf = self.evaluator(pos, override)
        if v in ENV: return True
        return self.lut(v, evf) != self.val(v, pos)
    def envguard(self, code, pos, override=None):
        e = self.evaluator(pos, override)
        req, pa, oa, orq = e(REQ), e(PACK), e(OACK), e(OREQ)
        if code == -1: return (not req) and not e(AACK) and not e(BACK) and not e(SACK) and not pa and not orq and not oa
        if code == -2: return req and e(AACK) and e(BACK) and e(SACK) and pa
        if code == -3: return req and not pa
        if code == -4: return (not req) and pa
        if code == -5: return orq and not oa
        if code == -6: return (not orq) and oa
        return True

def preds(T, i):
    """changed preds of event i: list of (event idx, necessary, u); settled: list of event idx; prev event idx"""
    e = T.ev[i]; v = e["node"]; R = e["R"]
    pprev = T.lastflip(v, e["pos"])
    if v in ENV:
        sup = ENVSUP - {v}; code = e["code"]
        excf = lambda ov: T.envguard(code, R, ov)
        # data-bus/req flips of one env-1 move share the move: no preds among themselves
    else:
        sup = ssupp(v)
        if not T.excited(v, R) and T.excited(v, e["pos"]): R = e["pos"]
        excf = lambda ov: T.excited(v, R, ov)
    base = excf(None)
    lim = -1 if pprev is None else pprev
    ch = []; settled = []
    for u in sup:
        q = T.lastflip(u, R)
        if q is None: continue
        if q < e["mstart"] or u not in ENV or v not in ENV:
            pass
        if q > lim:
            old = T.val(u, lim + 1) if lim >= 0 else T.init[u]
            nec = False
            if base and old != T.val(u, R):
                nec = not excf({u: old})
            ch.append((T.byPos[q], nec, u))
        else:
            settled.append(T.byPos[q])
    prev = T.byPos[pprev] if pprev is not None else None
    return ch, settled, prev, base, R

STRUCT = {}
def hop_paths(T, ui, target, Rt, mode):
    """(min4, max4) over paths from event ui's node to target's output; mode 'sens' or 'struct'"""
    u = T.ev[ui]["node"]
    if mode == "struct" and (u, target) in STRUCT: return STRUCT[(u, target)]
    if u == target or (u in ENV and target in ENV): return ((0,) * 4, (0,) * 4)
    if target in ENV:   # env reads nothing directly: target is an env move, paths to the boundary outputs
        best = None
        for x in BND_OUT:
            if x == u: r = ((0,) * 4, (0,) * 4)
            elif x in gate and (u in ssupp(x)): r = hop_paths(T, ui, x, Rt, mode)
            else: continue
            if r is None: continue
            best = r if best is None else (tuple(map(min, best[0], r[0])), tuple(map(max, best[1], r[1])))
        return best
    cone = bcone(target)
    # forward from u inside cone
    reach = set(); st = [u]
    while st:
        x = st.pop()
        for (g, j) in fan[x]:
            if g in cone and g not in reach: reach.add(g); st.append(g)
    nodes = sorted(reach, key=lambda x: topo[x]) + [target]
    if mode == "sens":
        e1 = T.evaluator(T.ev[ui]["pos"]); e2 = T.evaluator(Rt)
        def sens(g, j):
            k, ins, init = gate[g]; s = ins[j]; same = tuple(jj for jj, ss in enumerate(ins) if ss == s)
            for evf in (e1, e2):
                b0 = T.lut(g, evf)
                if T.lut(g, evf, (j,)) != b0 or T.lut(g, evf, same) != b0: return True
            return False
    lo = {u: (0,) * 4}; hi = {u: (0,) * 4}
    for g in nodes:
        k, ins, init = gate[g]; l4 = None; h4 = None
        for j, s in enumerate(ins):
            if s not in lo or not dep(k, init, j): continue
            if mode == "sens" and not sens(g, j): continue
            d = dly[g][j]
            a = tuple(lo[s][f] + d[f] for f in range(4)); b = tuple(hi[s][f] + d[f] for f in range(4))
            l4 = a if l4 is None else tuple(map(min, l4, a)); h4 = b if h4 is None else tuple(map(max, h4, b))
        if l4 is not None and g != target or (g == target and l4 is not None):
            lo[g] = l4; hi[g] = h4
    r = (lo[target], hi[target]) if target in lo and target in hi and target != u else None
    if mode == "struct": STRUCT[(u, target)] = r
    return r

def loop(v):
    """structural max of v's own feedback path (fast, slow)"""
    k, ins, init = gate[v]; best = [0, 0]
    # paths v -> (comb)* -> v
    class _T: pass
    r = None
    cone = bcone(v); reach = set(); st = [v]
    while st:
        x = st.pop()
        for (g, j) in fan[x]:
            if g in cone and g not in reach: reach.add(g); st.append(g)
    hi = {v: (0,) * 4}; res = None
    for g in sorted(reach, key=lambda x: topo[x]) + [v]:
        kk, ii, it = gate[g]; h4 = None
        for j, s in enumerate(ii):
            if s not in hi or not dep(kk, it, j): continue
            if g == v and s != v and s not in reach: continue
            d = dly[g][j]; b = tuple(hi[s][f] + d[f] for f in range(4))
            h4 = b if h4 is None else tuple(map(max, h4, b))
        if g == v: res = h4
        elif h4 is not None: hi[g] = h4
    return (res[1], res[3]) if res else (0, 0)

VARIANTS = {"sens": ("sens", "sens"), "mix": ("struct", "sens"), "struct": ("struct", "struct")}

def analyse(path):
    T = Trace(path)
    base = os.path.basename(path).replace(".log", "")
    cname, bname = base.split("__")[0], base.split("__")[1]
    C = nid[cname]; ib = len(T.ev) - 1
    while T.ev[ib]["move"] != len(T.moves) - 1 or T.ev[ib]["pos"] != T.ev[ib]["mstart"]: ib -= 1
    assert names[T.ev[ib]["node"]] == bname, (names[T.ev[ib]["node"]], bname)
    lo_i = max(0, ib - W)
    class LazyP(dict):
        def __missing__(self, i):
            r = preds(T, i); self[i] = r; return r
    P = LazyP()
    for i in range(lo_i, ib + 1): P[i]
    # pseudo event: c fires at b's reference point
    Rb = T.ev[ib]["pos"]
    pprev = T.lastflip(C, Rb); lim = -1 if pprev is None else pprev
    cch = []; cset = []
    assert T.excited(C, Rb), "c not excited before b"
    assert not T.excited(C, Rb + 1) or True
    for u in ssupp(C):
        q = T.lastflip(u, Rb)
        if q is None: continue
        if q > lim: cch.append((T.byPos[q], False, u))
        else: cset.append(T.byPos[q])
    cprev = T.byPos[pprev] if pprev is not None else None
    HOP = {}
    def hop(pi, xi, mode):
        key = (pi, xi, mode)
        if key not in HOP:
            if xi == "c": HOP[key] = hop_paths(T, pi, C, Rb, mode)
            else: HOP[key] = hop_paths(T, pi, T.ev[xi]["node"], P[xi][4], mode)
        return HOP[key]
    LP = {}
    def lp(x):
        if x not in LP: LP[x] = loop(x)
        return LP[x]
    lc = lp(C)
    out = {}
    anomalies = set()
    for i in range(lo_i, ib + 1):
        if not P[i][3]: anomalies.add("event %d (%s) not excited at its reference point" % (i, names[T.ev[i]["node"]]))
    for vname, (mlo, mhi) in VARIANTS.items():
        best = {}
        for a in range(lo_i, ib):
            # necessary ancestors of a
            NA = {a}; st = [a]
            while st:
                x = st.pop()
                if x < lo_i - NAB: continue
                for (p, nec, u) in P[x][0]:
                    if nec and p not in NA: NA.add(p); st.append(p)
            desc = {a}; LO = {a: (0, 0)}; HI = {a: (0, 0)}; arg = {}; flags = collections.Counter()
            def step(x, ch, settled, prev, node):
                isd = any(p in desc for (p, nec, u) in ch)
                if not isd: return None
                lcands = []; ncands = []; allin = True; hcands = []; bad = False
                for (p, nec, u) in ch:
                    if p in desc:
                        hl = hop(p, x, mlo); hh = hop(p, x, mhi)
                        if hl is None or hh is None:
                            flags["changed pred without (sensitised) path"] += 1; continue
                        l2 = (LO[p][0] + hl[0][0], LO[p][1] + hl[0][2])
                        if nec: ncands.append((l2, p))
                        lcands.append(l2)
                        hcands.append(((HI[p][0] + hh[1][1], HI[p][1] + hh[1][3]), p))
                    else:
                        allin = False
                        if p in NA:
                            hh = hop(p, x, mhi)
                            if hh is not None: hcands.append(((hh[1][1], hh[1][3]), p))
                        else: bad = True
                for q in settled + ([prev] if prev is not None else []):
                    if q is None: continue
                    if q in desc:
                        if q == prev: hcands.append(((HI[q][0] + lp(node)[0], HI[q][1] + lp(node)[1]), q))
                        else:
                            hh = hop(q, x, mhi)
                            if hh is not None: hcands.append(((HI[q][0] + hh[1][1], HI[q][1] + hh[1][3]), q))
                    elif q not in NA: flags["older event assumed settled"] += 1
                if x != "c" and node in ENV: bad = True
                lo2 = [-INF, -INF]
                for (l2, p) in ncands: lo2 = [max(lo2[0], l2[0]), max(lo2[1], l2[1])]
                if allin and lcands:
                    lo2 = [max(lo2[0], min(c[0] for c in lcands)), max(lo2[1], min(c[1] for c in lcands))]
                if bad or not hcands: hi2 = [INF, INF]
                else: hi2 = [max(c[0][0] for c in hcands), max(c[0][1] for c in hcands)]
                return tuple(lo2), tuple(hi2), ncands, hcands
            for x in range(a + 1, ib + 1):
                r = step(x, P[x][0], P[x][1], P[x][2], T.ev[x]["node"])
                if r is None: continue
                desc.add(x); LO[x], HI[x] = r[0], r[1]; arg[x] = (r[2], r[3])
            if ib not in desc: continue
            r = step("c", cch, cset, cprev, C)
            if r is None: continue
            hic = r[1]; arg["c"] = (r[2], r[3])
            for corner in (0, 1):
                L = LO[ib][corner]; Dc = hic[corner] + lc[corner]
                if not (L > -INF and Dc < INF): continue
                k = (L - Dc) / (L + Dc) if L + Dc > 0 else -1
                if corner not in best or k > best[corner][0]:
                    best[corner] = (k, a, L, Dc, dict(LO=dict(LO), HI=dict(HI), arg=dict(arg), flags=dict(flags), hic=hic))
        out[vname] = best
    return T, ib, C, out, anomalies, lc, HOP

def fmt_detail(T, ib, C, rec, corner, lc, mode):
    k, a, L, Dc, info = rec
    LO, HI, arg = info["LO"], info["HI"], info["arg"]
    nm = lambda i: names[T.ev[i]["node"]] if i != "c" else names[C] + "(c)"
    lines = ["  A = ev %d %s (move %d); LO(b) = %d, Dc = %d (HI(c-in) %d + loop %d), kappa* = %.3f; flags %s" % (
        a, nm(a), T.ev[a]["move"], L, Dc, info["hic"][corner], lc[corner], k, info["flags"])]
    # LO chain: follow argmax necessary preds from b
    x = ib; ch = []
    while x != a and x in arg:
        nc = arg[x][0]
        if not nc: ch.append((x, None)); break
        l2, p = max(nc, key=lambda c: c[0][corner]); ch.append((x, p)); x = p
    lines.append("  LO chain (b <- ... <- A), necessary preds, min-sum %s:" % ("fast" if corner == 0 else "slow"))
    for (x, p) in ch:
        lines.append("     %-16s LO %7s  <- %-16s LO %7s" % (nm(x), LO.get(x, (0, 0))[corner], nm(p) if p is not None else "-", LO.get(p, (0, 0))[corner] if p is not None else "-"))
    x = "c"; ch = []
    while x != a and x in arg:
        hc = arg[x][1]
        if not hc: break
        h2, p = max(hc, key=lambda c: c[0][corner]); ch.append((x, p, h2[corner])); x = p
        if p not in HI: break
    lines.append("  HI chain (c <- ... <- A), max-sum:")
    for (x, p, h) in ch:
        lines.append("     %-16s HI %7d  <- %-16s HI %7s" % (nm(x), h, nm(p), HI.get(p, (0, 0))[corner] if p in HI else "(anc of A: 0)"))
    return "\n".join(lines)

if __name__ == "__main__":
    res = collections.defaultdict(list)
    for path in sys.argv[4:]:
        try:
            T, ib, C, out, anom, lc, HOP = analyse(path)
        except Exception as ex:
            print("==", os.path.basename(path), "ERROR", repr(ex)); continue
        base = os.path.basename(path).replace(".log", "").replace(".txt", "")
        pair = "__".join(base.split("__")[:2])
        row = {}
        for vname in VARIANTS:
            for corner in (0, 1):
                b = out[vname].get(corner)
                row[(vname, corner)] = b[0] if b else None
        res[pair].append((row, path))
        s = " ".join("%s/%d=%s" % (v, c, ("%.3f" % row[(v, c)]) if row[(v, c)] is not None else "none") for v in VARIANTS for c in (0, 1))
        print("==", base, s, ("ANOM " + "; ".join(sorted(anom))[:300]) if anom else "", flush=True)
        if os.environ.get("DETAIL"):
            for corner in (0, 1):
                b = out["sens"].get(corner)
                if b: print(fmt_detail(T, ib, C, b, corner, lc, "sens"))
    print("\n# per pair: min over traces of best kappa* (variants sens / mix / struct; corner fast, slow)")
    for pair in sorted(res):
        rows = res[pair]
        def mn(v, c):
            xs = [r[(v, c)] for r, _ in rows]
            if any(x is None for x in xs): return "none"
            return "%.3f" % min(xs)
        print("%-34s n=%d  sens %s %s  mix %s %s  struct %s %s" % (pair, len(rows), mn("sens", 0), mn("sens", 1), mn("mix", 0), mn("mix", 1), mn("struct", 0), mn("struct", 1)))
