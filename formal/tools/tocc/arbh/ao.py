#!/usr/bin/env python3
"""Shard C (UNTRUSTED): the (12,18) certificate against Formal/Net/AO/Timed.lean (AND-OR causes, per-reader L,
TOA, SepOKA, UpOKA, hRT).  usage: ao.py c [rounds]
CP (physical cert): event (v,k) of an exact gate at time t, previous event at tp (t0 for k=0).  Candidate causes
S = for each exact live source w whose value AS READ BY v (mid delays) differs between tp and t, the latest event of
w read in (tp, t].  Alternatives = the minimal subsets A of S such that F(sources in A at their read value at t,
all other sources at their read value at tp) != v's value before the event.  The previous event (v,k-1) is NOT in
the alternatives (it is LStep's/SepOKA's/UpOKA's separate "previous event" clause; Enabled needs n v = k anyway).
Env events: one alternative (the env rule's read set, as before); rst: one empty alternative.
CF = CP + RT edges (an RT edge U -> W is appended to every alternative of W).
Order bound VC_CF(e) = max(VC(prev), min over alts of max over causes VC(p)), own count k+1 (LStep form).
Sep (SepOKA): forms ii (min over CP alternatives of max over its causes, + lo'), iii (previous event, + lo'(a,a)), iv (common ancestor
e0, tm e0 < tm(b,m): Sep(e0->(a,k)) - Up(e0->(b,m)), needs >= 1; computed one level only, not nested).
Up (UpOKA): e = e0, or an exact GATE event with SOME CP alternative all of whose causes have Up, plus (k > 0) its
previous event having Up: Up = max(prev + hi'(v,v), min over such alts of max(Up(p) + hi'(v,p))).
TOA: rows a != b; a row with a = v is exempt if for some k' <= k every CP alternative of (v,k') has a cause (b,m')
with L v v k b <= m'+1; otherwise Sep >= hi'(v,b) - lo'(v,a).  Failing rows: L v (a,k,b) lowered (this reader only)
to the largest value whose row passes.  RT edges: from LCheck failures, pair U=(u,n_u), W=(w,n_w-1) in D v, U not
below W in CF; justified iff form-iv bound >= max(1, hi'(v,u) - lo'(v,w)); added to CF; repeat rounds."""
import sys, time, pickle, collections, functools
import numpy as np
from bisect import bisect_right
sys.path.insert(0, "/tmp/claude-0/arbh")
from classify import load, lut
from cert import ENVREAD
INF = float("inf")
c = int(sys.argv[1]); ROUNDS = int(sys.argv[2]) if len(sys.argv) > 2 else 3
NOPREV = "--noprev" in sys.argv
LEGACY = "--legacy" in sys.argv
PREVANC = ("--prevanc" in sys.argv) or not LEGACY
ROBUST = "--robust" in sys.argv; nrob = [0]
import os; ROBNODES = set(x for x in os.environ.get("ROBNODES", "").split(",") if x)
CAUSEANC = ("--causeanc" in sys.argv) or not LEGACY   # repair candidate: a previous event causally below e0 counts as Up hi'(v,v)     # diagnostic: Up without UpOKA's previous-event clause
T0 = time.time()
C = load(); g = C["gates"]; EX = C["EXACT"]; bs = C["bs"]; nm = C["names"]; DATA = C["DATA"]
H = pickle.load(open("/tmp/claude-0/arbh/hist_c%d%s.pkl" % (c, __import__("os").environ.get("PAIR", "")), "rb")); R = H["R"]; t0 = R - 1; hist = H["hist"]
def valat(n, t):
    if n not in hist: return False
    b, ts = hist[n]; return b ^ (bisect_right(ts, t) % 2 == 1)
ev = {n: [x for x in (hist[n][1] if n in hist else []) if x > t0] for n in EX}
s0 = {n: valat(n, t0) for n in EX}
envnode = {bs[k]: k for k in ENVREAD}
dl = {}
for v in EX:
    if v in envnode: continue
    for p in C["live"][v]: dl[(v, p["src"])] = p["win"][c]
def lo_(v, w): return dl[(v, w)][0] if (v, w) in dl else 1
def hi_(v, w): return dl[(v, w)][1] if (v, w) in dl else 1
eid = {}; el = []
for n in sorted(EX):
    for k, t in enumerate(ev[n]): eid[(n, k)] = len(el); el.append((n, k, t))
NE = len(el)
xs = sorted(EX); xi = {n: i for i, n in enumerate(xs)}
enode = np.array([xi[n] for n, k, t in el], dtype=np.int32); ek = np.array([k for n, k, t in el], dtype=np.int32)
et = np.array([t for n, k, t in el], dtype=np.int64)
prev = [eid[(n, k - 1)] if k else None for n, k, t in el]
# ---------------- CP alternatives
PAIRSUF = __import__("os").environ.get("PAIR", "")
DCP = "--nodcp" not in sys.argv; carry = {}; dcp_stat = collections.Counter()
alts = [None] * NE; nalt = collections.Counter(); bad_full = 0
for e, (v, k, t) in enumerate(el):
    tp = ev[v][k - 1] if k else t0
    if v in envnode:
        cs = []
        for key in ENVREAD[envnode[v]]:
            w = bs[key]; tw = ev[w]; i = bisect_right(tw, t - 1) - 1
            if i >= 0 and tw[i] > tp: cs.append(eid[(w, i)])
        alts[e] = [cs]; nalt[1] += 1; continue
    pins = g[v]["pins"]; tn = ev[v][k + 1] if k + 1 < len(ev[v]) else 10**12
    S = []; AH = []
    for p in C["live"][v]:
        w = p["src"]
        if w == v or w not in EX: continue
        d = p["win"][c][2]; tw = ev[w]
        i = bisect_right(tw, t - d) - 1
        if i >= 0 and tw[i] + d > tp: S.append((w, eid[(w, i)], valat(w, tw[i])))
        elif i + 1 < len(tw) and tw[i + 1] + d <= tn: AH.append((w, eid[(w, i + 1)], valat(w, tw[i + 1])))
    P = S + AH
    def F(A, ov=None):
        post = {w: val for (w, _, val) in A}; bits = []
        for p in pins:
            w = p["src"]; d = p["win"][c][2]
            if w == v: bits.append(valat(v, tp))
            elif w in post: bits.append(post[w])
            elif ov and w in ov: bits.append(ov[w])
            else: bits.append(valat(w, tp - d))
        return bool(lut(g[v]["init"], g[v]["k"], bits))
    before = not valat(v, t)
    en = []
    for mask in range(1 << len(P)):
        if F([P[i] for i in range(len(P)) if mask >> i & 1]) != before: en.append(mask)
    mins = [m for m in en if not any((o & m) == o and o != m for o in en)]
    nS = len(S); smask = (1 << nS) - 1
    mins = [m for m in mins if m & smask or True]
    if not any(m & ~smask == 0 for m in mins):
        bad_full += 1; mins = [smask] + [m for m in mins if m & ~smask]
    used = 0
    for m in mins: used |= m
    rest = [S[i][1] for i in range(nS) if not used >> i & 1]
    if ROBUST or nm[v] in ROBNODES:
        # alternative M is robust if F flips for EVERY value (pre or post) of the other pool members
        full = (1 << len(P)) - 1
        def robust(m):
            comp = full & ~m
            sub = comp
            while True:
                if F([P[i] for i in range(len(P)) if (m | sub) >> i & 1]) == before: return False
                if sub == 0: return True
                sub = (sub - 1) & comp
        rob = [m for m in range(1 << len(P)) if robust(m)]
        rmins = [m for m in rob if not any((o & m) == o and o != m for o in rob)]
        if rmins and any(m & ~smask == 0 for m in rmins):
            mins = rmins; rest = []; nrob[0] += 1
    if DCP:
        # don't-care placement: an absorbed change (in S but in no minimal set) is not a cause here; it is carried
        # to the first later event of v whose alternative stops enabling when the change is reverted
        if k == 0: carry[v] = []
        altsE = [[P[i][1] for i in range(len(P)) if m >> i & 1] for m in mins]
        keep = []
        for (w, r, preval) in carry[v]:
            if any(x[0] == w for x in S): dcp_stat["superseded"] += 1; continue
            need = False
            for ai, m in enumerate(mins):
                if F([P[i] for i in range(len(P)) if m >> i & 1], {w: preval}) == before:
                    altsE[ai].append(r); need = True
            if need: dcp_stat["placed"] += 1
            else: keep.append((w, r, preval))
        if k + 1 == len(ev[v]): dcp_stat["dropped_at_end"] += len(keep); keep = []
        newc = []
        for i in range(nS):
            if used >> i & 1: continue
            w, r, post = S[i]; dw = dl[(v, w)][2]
            netchg = valat(w, tp - dw) != post
            needs = [ai for ai, m in enumerate(mins) if F([P[q] for q in range(len(P)) if m >> q & 1], {w: not post}) == before]
            if netchg and not needs and k + 1 < len(ev[v]):
                newc.append((w, r, not post)); dcp_stat["carried"] += 1
            elif netchg and not needs:
                dcp_stat["dropped (don't-care at v's last event)"] += 1
            elif netchg and needs:
                for ai in needs: altsE[ai].append(r)
                dcp_stat["appended to the alternatives needing it"] += 1
            else:
                for a_ in altsE: a_.append(r)
                dcp_stat["appended to all (pulse, or last event)"] += 1
        carry[v] = keep + newc
        if k + 1 == len(ev[v]): dcp_stat["dropped_at_end"] += len(carry[v]); carry[v] = []
        alts[e] = altsE
    else:
        alts[e] = [[P[i][1] for i in range(len(P)) if m >> i & 1] + rest for m in mins]
    nalt[len(mins)] += 1
# acyclicity: Kahn over prev + all alternative causes; drop look-ahead alternatives on cycles
def topo():
    indeg = [0] * NE; succ = [[] for _ in range(NE)]
    for e in range(NE):
        ps = set(p for alt in alts[e] for p in alt)
        if prev[e] is not None: ps.add(prev[e])
        for p in ps: succ[p].append(e); indeg[e] += 1
    q = [e for e in range(NE) if indeg[e] == 0]; out = []
    while q:
        x = q.pop(); out.append(x)
        for y in succ[x]:
            indeg[y] -= 1
            if indeg[y] == 0: q.append(y)
    return out, indeg
dropped = 0
CYC = ("--cyc" in sys.argv) or not LEGACY     # cut one alternative per found cycle (the most anticipatory one) instead of all later ones
if not CYC:
  while True:
    out, indeg = topo()
    if len(out) == NE: break
    cyc = [e for e in range(NE) if indeg[e] > 0]
    ch = False
    for e in cyc:
        te = el[e][2]
        keep = [alt for alt in alts[e] if all(el[p][2] < te for p in alt)]
        if len(keep) < len(alts[e]) and keep: dropped += len(alts[e]) - len(keep); alts[e] = keep; ch = True
    if not ch: raise SystemExit("cycle not resolved")
else:
  sys.setrecursionlimit(100000)
  while True:
    out, indeg = topo()
    if len(out) == NE: break
    rem = set(e for e in range(NE) if indeg[e] > 0)
    # find one cycle among remaining nodes: walk predecessors (causes) inside rem
    def preds(e):
        ps = [(p, ai) for ai, alt in enumerate(alts[e]) for p in alt if p in rem]
        if prev[e] is not None and prev[e] in rem: ps.append((prev[e], None))
        return ps
    start = next(iter(rem)); seen = {}; path = []; x = start
    while x not in seen:
        seen[x] = len(path); ps = preds(x)
        p, ai = ps[0]; path.append((x, p, ai)); x = p
    cycle = path[seen[x]:]
    cand = [(el[p][2] - el[e][2], e, ai) for (e, p, ai) in cycle if ai is not None and len(alts[e]) > 1]
    if not cand: raise SystemExit("cycle without a removable alternative")
    _, e, ai = max(cand)
    alts[e] = alts[e][:ai] + alts[e][ai + 1:]; dropped += 1
tm = [0] * NE
for i, e in enumerate(out): tm[e] = i
tm = np.array(tm, dtype=np.int64)
order = list(out)
print("  look-ahead alternatives dropped for cycles: %d; events with robust alternatives: %d; don't-care placement %s" % (dropped, nrob[0], dict(dcp_stat)))
print("[c=%d] events %d; alternatives per event %s; events whose full candidate set does not enable (fallback AND): %d" % (
    c, NE, sorted(nalt.items()), bad_full))
# common causes (in every CP alternative)
BCP = "--bcp" in sys.argv
if BCP:
    # (b') put source b's event into EVERY CP alternative of an OR event of v when b's event is below the event in
    # every ideal of the plain order and v read it (sim, mid delay) no later than the event fired
    VC0 = None
    def _vc():
        VC = np.zeros((NE, len(xs)), dtype=np.int8)
        for e in order:
            n, k, t = el[e]; row = VC[e]; best = None
            for alt in alts[e]:
                r = np.zeros(len(xs), dtype=np.int8)
                for p in alt: np.maximum(r, VC[p], out=r)
                best = r if best is None else np.minimum(best, r)
            if best is not None: np.maximum(row, best, out=row)
            if prev[e] is not None: np.maximum(row, VC[prev[e]], out=row)
            row[xi[n]] = k + 1
        return VC
    VC0 = _vc(); nb_mid = 0; nb_win = 0
    for e in range(NE):
        v, k, t = el[e]
        if len(alts[e]) < 2 or v in envnode: continue
        for p in C["live"][v]:
            b = p["src"]
            if b == v or b not in EX: continue
            mm = int(VC0[e, xi[b]])
            if mm == 0: continue
            pb = eid[(b, mm - 1)]
            if all(pb in a for a in alts[e]): continue
            if et[pb] + p["win"][c][2] <= t:
                nb_mid += 1
                if et[pb] + p["win"][c][1] <= t: nb_win += 1
                alts[e] = [a if pb in a else a + [pb] for a in alts[e]]
    print("  --bcp: b added to every alternative at %d OR events (read before the event even at hi: %d)" % (nb_mid, nb_win))
common = [set(a[0]).intersection(*map(set, a[1:])) if a else set() for a in alts]
# ---------------- order bound (CF = CP + rt)
def vclock(rt):
    VC = np.zeros((NE, len(xs)), dtype=np.int8)
    for e in order:
        n, k, t = el[e]; row = VC[e]
        best = None
        for alt in alts[e]:
            a2 = alt + rt.get(e, [])
            r = np.zeros(len(xs), dtype=np.int8)
            for p in a2: np.maximum(r, VC[p], out=r)
            best = r if best is None else np.minimum(best, r)
        if best is not None: np.maximum(row, best, out=row)
        if prev[e] is not None: np.maximum(row, VC[prev[e]], out=row)
        row[xi[n]] = k + 1
    return VC
VCP = vclock({})
def leqP(a, b): return VCP[b, enode[a]] > ek[a]
# ---------------- Sep (forms ii, iii) and Up
def wlo(v, w):
    if v in envnode: return 1
    if v == w: return lo_(v, v) if (v, v) in dl else 1
    return lo_(v, w)
def whi(v, w):
    if v == w: return hi_(v, v) if (v, v) in dl else 1
    return hi_(v, w)
@functools.lru_cache(maxsize=200000)
def sep23(s, T):
    """Sep(s -> T) by forms ii/iii only (None if no such path)"""
    if s == T: return 0
    if not leqP(s, T): return None
    de = VCP[:, enode[s]] > ek[s]          # s below e in every ideal (necessary for Sep)
    idx = np.nonzero(de & (tm <= tm[T]) & (tm >= tm[s]))[0]; idx = idx[np.argsort(tm[idx], kind="stable")]
    S = {}
    for e in idx:
        e = int(e)
        if e == s: S[e] = 0; continue
        v = el[e][0]; best = None; f2 = None
        for alt in alts[e]:
            xa = None
            for p in alt:
                if p in S:
                    x = S[p] + wlo(v, el[p][0]); xa = x if xa is None or x > xa else xa
            if xa is None: f2 = None; break
            f2 = xa if f2 is None or xa < f2 else f2
        if alts[e] and f2 is not None: best = f2
        pp = prev[e]
        if pp is not None and pp in S:
            x = S[pp] + wlo(v, v); best = x if best is None or x > best else best
        if best is not None: S[e] = best
    return S.get(T)
upcache = {}
def up_from(e0, horizon):
    """UpOKA-style upper bounds from e0 for events with time in [tau(e0), horizon]"""
    key = e0
    if key in upcache and upcache[key][0] >= horizon: return upcache[key][1]
    U = {e0: 0}
    for e in ord_arr[int(tm[e0]):int(horizon) + 1]:
        e = int(e)
        if e == e0 or e in U: continue
        v, k, t = el[e]
        if v in envnode or v not in g: continue
        pr = 0
        if k > 0:
            if prev[e] in U: pr = U[prev[e]] + whi(v, v)
            elif NOPREV: pr = 0
            elif PREVANC and sep23(prev[e], e0) is not None: pr = whi(v, v)   # Lean UpOKA 2nd disjunct: Sep (v,k-1)->e0 exists
            else: continue
        ba = None
        for alt in alts[e]:
            if not alt: continue
            if CAUSEANC:   # proposed: a cause with a Sep entry to e0 happened before e0, counts as hi' only
                if not all(p in U or sep23(p, e0) is not None for p in alt): continue
                x = max((U[p] if p in U else 0) + whi(v, el[p][0]) for p in alt)
            else:
                if not all(p in U for p in alt): continue
                x = max(U[p] + whi(v, el[p][0]) for p in alt)
            ba = x if ba is None or x < ba else ba
        if ba is None and not (NOPREV and False): continue
        U[e] = max(pr, ba)
    upcache[key] = (horizon, U); return U
ord_arr = np.array(order, dtype=np.int64)
DEEP = "--deep" in sys.argv
@functools.lru_cache(maxsize=200000)
def form4(B, A, ncand=None):
    ncand = ncand or (60 if DEEP else 10)
    """best Sep(B -> A) by form iv: max over recent common ancestors e0 (tm e0 < tm B) of Sep23(e0->A) - Up(e0->B)"""
    m = np.minimum(VCP[A], VCP[B]); best = (-INF, None)
    cands = []
    for x in np.nonzero(m)[0]:
        for back in ((1, 2, 3) if DEEP else (1,)):
            if int(m[x]) - back < 0: continue
            e0 = eid[(xs[x], int(m[x]) - back)]
            if tm[e0] < tm[B]: cands.append((tm[e0], e0))
    # also: B's own earlier causes chain is covered by common ancestors
    cands.sort(reverse=True)
    for _, e0 in cands[:ncand]:
        s = sep23(e0, A)
        if s is None: continue
        U = up_from(e0, int(tm[B]))
        if B not in U: continue
        if s - U[B] > best[0]: best = (s - U[B], e0)
    return best
def sepAny(B, A):
    s = sep23(B, A)
    f, e0 = form4(B, A)
    return max(s if s is not None else -INF, f), (s is not None and s >= f)
# ---------------- data reads, D, local check
def Dof(v):
    if v in envnode: return [v] + [bs[k] for k in ENVREAD[envnode[v]]]
    D = [v]
    for p in C["live"][v]:
        w = p["src"]
        if w in EX and w not in D: D.append(w)
    for k in range(len(ev[v])):
        for alt in alts[eid[(v, k)]]:
            for p in alt:
                if el[p][0] not in D: D.append(el[p][0])
    return D
DATAG = pickle.load(open("/tmp/claude-0/arbh/data_c%d%s.pkl" % (c, __import__("os").environ.get("PAIR", "")), "rb"))["guards"]
def env_en(v, s, n):
    kind = envnode[v]
    if kind == "rst": return s[v]
    if kind == "pend_ack": return s[v] != s[bs["req"]]
    if kind == "out0_ack": return s[v] != s[bs["out0_req"]]
    acks = [s[bs[x]] for x in ("a_ack", "b_ack", "start_ack")]
    if not s[v]: return (not any(acks)) and n[v] == 0
    return all(acks)
def check(v, Lv):
    D = Dof(v); lens = [len(ev[u]) for u in D]; m = len(D)
    Bt = [[[(Lv(D[i], k, D[j]) if i != j else 0) for j in range(m)] for k in range(lens[i])] for i in range(m)]
    isenv = v in envnode
    if not isenv:
        pk = []
        for p in g[v]["pins"]:
            w = p["src"]
            if not p["live"] or w in C["const"]: pk.append(("c", valat(w, t0)))
            elif w in EX: pk.append(("x", D.index(w)))
            else: pk.append(("d", w))
        dpins = sorted(set(x[1] for x in pk if x[0] == "d"))
    altsv = [[[(D.index(el[p][0]), el[p][1]) for p in alt] for alt in alts[eid[(v, k)]]] for k in range(lens[0])]
    n = [0] * m; out = []; cnt = [0]
    def okp(i):
        ni = n[i]
        if ni > 0:
            row = Bt[i][ni - 1]
            for j in range(i):
                if row[j] > n[j]: return False
        for j in range(i):
            if n[j] > 0 and Bt[j][n[j] - 1][i] > ni: return False
        return True
    def evaluate():
        s = {D[j]: s0[D[j]] ^ (n[j] & 1) for j in range(m)}
        if isenv: exc = {bool(env_en(v, s, dict(zip(D, n))))}
        else:
            dv = {}
            for z in dpins:
                for (st, en, val) in DATAG.get((v, z), ()):
                    if (st is None or st[1] < n[D.index(st[0])]) and (en is None or n[D.index(en[0])] <= en[1]):
                        dv[z] = val; break
            free = [z for z in dpins if z not in dv]; exc = set()
            for mask in range(1 << len(free)):
                bb = dict(dv)
                for q, z in enumerate(free): bb[z] = bool(mask >> q & 1)
                bits = [(x[1] if x[0] == "c" else (s[D[x[1]]] if x[0] == "x" else bb[x[1]])) for x in pk]
                exc.add(bool(lut(g[v]["init"], g[v]["k"], bits)) != s[v])
                if len(exc) == 2: break
        nv = n[0]
        enab = nv < lens[0] and any(all(i < n[j] for (j, i) in alt) for alt in altsv[nv])
        kind = "X" if len(exc) == 2 else ("EnE" if exc == {True} and not enab else ("NxE" if exc == {False} and enab else None))
        if kind:
            own = all(any(all(i < n[j] for (j, i) in alt) for alt in altsv[k]) for k in range(n[0]))
            out.append((kind if own else kind + "~", tuple(n)))
    def rec(i):
        if i == m: cnt[0] += 1; evaluate(); return
        for x in range(lens[i] + 1):
            n[i] = x
            if okp(i): rec(i + 1)
        n[i] = 0
    rec(0)
    return D, cnt[0], out
# ---------------- rounds
rt = {}   # W -> [U]
rtinfo = {}
for rnd in range(ROUNDS + 1):
    VC = vclock(rt)
    nrows = 0; rows_fail = []; rows_exempt = 0; rows_sep4 = 0; weak = 0
    nvec = 0; fails = []; maxD = 0
    for v in sorted(EX):
        D = Dof(v); maxD = max(maxD, len(D)); over = {}
        if v not in envnode:
            for a in D:
                for b in D:
                    if a == b: continue
                    need = whi(v, b) - (wlo(v, a) if a != v or (v, v) in dl else 1)
                    need = (hi_(v, b) if (v, b) in dl else 1) - (lo_(v, a) if (v, a) in dl else 1)
                    if need <= 0: continue
                    for k in range(len(ev[a])):
                        mm = int(VC[eid[(a, k)], xi[b]])
                        if mm == 0: continue
                        nrows += 1
                        def passes(mm):
                            if a == v:
                                for k2 in range(k + 1):
                                    if all(any(el[p][0] == b and mm <= el[p][1] + 1 for p in alt) for alt in alts[eid[(v, k2)]]):
                                        return "ex", None
                            s, via23 = sepAny(eid[(b, mm - 1)], eid[(a, k)])
                            return ("ok" if s >= need else "fail"), s
                        r, s = passes(mm)
                        if r == "ex": rows_exempt += 1; continue
                        if r == "ok":
                            if sep23(eid[(b, mm - 1)], eid[(a, k)]) is None or sep23(eid[(b, mm - 1)], eid[(a, k)]) < need: rows_sep4 += 1
                            continue
                        rows_fail.append((s - need if s > -INF else -INF, v, a, k, b, mm - 1, s, need))
                        m2 = mm - 1
                        while m2 > 0 and passes(m2)[0] == "fail": m2 -= 1
                        over[(a, k, b)] = m2; weak += 1
        Lv = lambda a, k, b, over=over: min(int(VC[eid[(a, k)], xi[b]]), over.get((a, k, b), 99))
        D, nv_, out = check(v, Lv); nvec += nv_
        fails += [(v, kind, nn, D) for kind, nn in out]
    fails_all = fails; fails = [f for f in fails if not f[1].endswith("~")]
    fc = collections.Counter(f[1] for f in fails)
    print("   (without the ownB filter: %d failures %s at %d nodes)" % (len(fails_all), dict(collections.Counter(f[1].rstrip("~") for f in fails_all)), len(set(f[0] for f in fails_all))))
    print("[c=%d round %d] RT edges %d | TO rows %d: exempt (a = v, own read) %d, pass (needing form iv: %d), FAIL %d -> L entries lowered %d | LCheckXA: vectors %d, max|D| %d, failures %d %s at %d nodes (%.0fs)" % (
        c, rnd, sum(len(x) for x in rt.values()), nrows, rows_exempt, rows_sep4, len(rows_fail), weak, nvec, maxD,
        len(fails), dict(fc), len(set(f[0] for f in fails)), time.time() - T0), flush=True)
    if rnd == ROUNDS: break
    # propose RT edges
    new = 0; unjust = []
    for (v, kind, nn, D) in fails:
        if kind == "X": continue
        best = None
        for iu, u in enumerate(D):
            if nn[iu] >= len(ev[u]): continue
            U = eid[(u, nn[iu])]
            for iw, w in enumerate(D):
                if iw == iu or nn[iw] == 0: continue
                W = eid[(w, nn[iw] - 1)]
                if VC[W, enode[U]] > ek[U]: continue
                if tm[U] >= tm[W]: continue        # must also respect time stamps (TmOK CF)
                f4, e0 = form4(U, W)
                if f4 == -INF: continue
                needr = max(1, (hi_(v, u) if (v, u) in dl else 1) - (lo_(v, w) if (v, w) in dl else 1))
                mg = f4 - needr
                if best is None or mg > best[0]: best = (mg, U, W, e0, f4, v)
        if best is not None and best[0] >= 0:
            mg, U, W, e0, f4, vv = best
            if U not in rt.get(W, []):
                rt.setdefault(W, []).append(U); new += 1
                rtinfo[(U, W)] = (mg, f4, vv, e0)
        else: unjust.append((v, kind, nn, best))
    print("   proposed RT edges this round: %d new; failures with no justified edge: %d" % (new, len(unjust)), flush=True)
# ---------------- report
print("TO rows failing (final round), worst 10:")
for r in sorted(rows_fail, key=lambda r: r[0])[:10]:
    m_, v, a, k, b, mb, s, need = r
    print("   margin %s  v=%s a=%s(%d) b=%s(%d) Sep=%s need=%d" % (m_, nm[v], nm[a], k, nm[b], mb, s, need))
print("RT edges: %d; reader margin min %s; hRT event-level Sep (form iv) min %s" % (
    len(rtinfo), min((x[0] for x in rtinfo.values()), default=None), min((x[1] for x in rtinfo.values()), default=None)))
for (U, W), (mg, f4, vv, e0) in sorted(rtinfo.items(), key=lambda x: x[1][0])[:10]:
    print("   %s(%d) -> %s(%d) at reader %s: reader margin %d, form-iv Sep %d, e0=%s(%d)" % (
        nm[el[U][0]], el[U][1], nm[el[W][0]], el[W][1], nm[vv], mg, f4, nm[el[e0][0]], el[e0][1]))
print("remaining failures (final round), sample:")
for (v, kind, nn, D) in [f for f in fails if f[1] != "X"][:12]:
    print("   %s %s %s n=%s D=%s" % (nm[v], "CTRL" if v in C["CTRL"] else "", kind, nn, [nm[u] for u in D]))
pickle.dump(dict(rt=rt, rtinfo=rtinfo, fails=fails, rows_fail=rows_fail, alts=alts, el=el, VC=VC, tm=tm), open("/tmp/claude-0/arbh/ao_c%d%s.pkl" % (c, ("_noprev" if NOPREV else ("_prevanc" if PREVANC else "")) + ("_deep" if DEEP else "") + ("_bcp" if BCP else "") + ("_cyc" if CYC else "") + ("_causeanc" if CAUSEANC else "") + ("_robust" if ROBUST else "") + ("_robn" if ROBNODES else "") + ("_dcp" if DCP else "") + PAIRSUF), "wb"))
