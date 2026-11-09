# Shard C (UNTRUSTED).  exec'd after ao.py's definitions (datal.py).  Replaces up_from/form4/sepAny with an Up builder
# that also uses UpOKA's RELATIVE clause (Timed.lean, def UpOKA, third disjunct for causes and for the previous event):
#   Up e0 e = d may justify a cause p by  Up a p = dA,  Sep a e0 = dS,  dA + hi'(e,p) <= d + dS.
# Every Up value carries its justification (J) so that emit() can write the tables and lchk.py can re-check them
# against a transcription of DecT.upFormB / sepFormB.
#   env REL=0 disables the relative clause (baseline), RELK = anchors tried per cause, RELD = recursion depth.
import os as _os
REL = _os.environ.get("REL", "1") == "1"
RELK = int(_os.environ.get("RELK", "8"))
RELD = int(_os.environ.get("RELD", "2")) if REL else 0
RELTRY = int(_os.environ.get("RELTRY", "24"))     # anchors examined per cause (with or without a Sep23 to e0)
CURD = [0]        # depth used by sepAny: 0 for claim building, RELD for the guard-facing queries (see datal.py)
SEPIV1 = _os.environ.get("SEPIV1", "1") == "1"     # form iv needs d >= 1 (SepOKA); the old sepAny did not enforce it
UPST = {}          # (e0, depth) -> dict(U=..., J=..., pos=index into ord_arr)
RELSTAT = collections.Counter()
# flat event table by (node index, k): event id of the k-th event of node x is FLAT[BASE[x] + k]
_cnt = np.zeros(len(xs), dtype=np.int64)
for _n, _k, _t in el: _cnt[xi[_n]] += 1
BASE = np.concatenate([[0], np.cumsum(_cnt)[:-1]]).astype(np.int64)
FLAT = np.zeros(NE, dtype=np.int64)
for _e, (_n, _k, _t) in enumerate(el): FLAT[BASE[xi[_n]] + _k] = _e
UNB = RELD >= 50          # unbounded recursion: tables keyed by e0 only (anchors are strictly earlier in tm)
def _anchors(p, e0):
    """the latest common causal ancestors of p and e0, one per node, newest (in tm) first"""
    m = np.minimum(VCP[p], VCP[e0]).astype(np.int64)
    nz = np.nonzero(m)[0]
    ids = FLAT[BASE[nz] + m[nz] - 1]
    ids = ids[(ids != e0) & (ids != p)]
    if len(ids) > RELTRY:
        part = np.argpartition(-tm[ids], RELTRY)[:RELTRY]; ids = ids[part]
    return [int(a) for a in ids[np.argsort(-tm[ids], kind="stable")]]
_relmemo = {}
def _rel(p, e0, depth):
    """min over anchors a of Up(a->p) - Sep23(a->e0); returns (value, a) or None"""
    key = (p, e0, depth)
    if key in _relmemo: return _relmemo[key]
    best = None; n = 0
    for a in _anchors(p, e0)[:RELTRY]:
        s = sep23(a, e0)
        if s is None: continue
        n += 1
        ua = up_get(a, p, depth if UNB else depth - 1)
        if ua is not None:
            x = ua - s
            if best is None or x < best[0]: best = (x, a)
        if n >= RELK: break
    _relmemo[key] = best
    return best
def _term(p, e0, depth, U, h):
    """best bound contribution of cause/prev p for Up(e0 -> .): (value, tag)"""
    best = None
    if p in U: best = (U[p] + h, ("U",))
    if sep23(p, e0) is not None:
        if best is None or h < best[0]: best = (h, ("S",))
    if best is None and depth > 0:      # the relative clause only where the absolute ones fail
        r = _rel(p, e0, depth)
        if r is not None:
            best = (r[0] + h, ("R", r[1], depth if UNB else depth - 1)); RELSTAT["relative clause used"] += 1
    return best
def _extend(e0, depth, horizon):
    key = (e0, depth)
    st = UPST.get(key)
    if st is None:
        st = dict(U={e0: 0}, J={e0: ("eq",)}, pos=int(tm[e0])); UPST[key] = st
    U = st["U"]; J = st["J"]
    while st["pos"] <= horizon and st["pos"] < NE:
        e = int(ord_arr[st["pos"]]); st["pos"] += 1
        if e == e0 or e in U: continue
        v, k, t = el[e]
        if v in envnode or v not in g: continue
        pr = 0; ptag = None
        if k > 0:
            r = _term(prev[e], e0, depth, U, whi(v, v))
            if r is None: continue
            pr, ptag = r
        ba = None
        for ai, alt in enumerate(alts[e]):
            if not alt: continue
            x = None; tags = []
            for p in alt:
                r = _term(p, e0, depth, U, whi(v, el[p][0]))
                if r is None: x = None; break
                tags.append(r[1]); x = r[0] if x is None or r[0] > x else x
            if x is None: continue
            if ba is None or x < ba[0]: ba = (x, ai, tags)
        if ba is None: continue
        U[e] = max(0, pr, ba[0]); J[e] = ("alt", ba[1], ba[2], ptag)
    return st
def up_get(e0, e, depth):
    if tm[e] < tm[e0]: return None if e != e0 else 0
    st = _extend(e0, depth, int(tm[e]))
    return st["U"].get(e)
def up_from(e0, horizon):     # compatibility
    return _extend(e0, CURD[0], int(horizon))["U"]
def form4(B, A, ncand=None, depth=None):
    return _form4(B, A, ncand, CURD[0] if depth is None else depth)
@functools.lru_cache(maxsize=400000)
def _form4(B, A, ncand, depth):
    ncand = ncand or (60 if DEEP else 10)
    m = np.minimum(VCP[A], VCP[B]); best = (-INF, None, None)
    cands = []
    for x in np.nonzero(m)[0]:
        for back in ((1, 2, 3) if DEEP else (1,)):
            if int(m[x]) - back < 0: continue
            e0 = eid[(xs[x], int(m[x]) - back)]
            if tm[e0] < tm[B]: cands.append((tm[e0], e0))
    cands.sort(reverse=True)
    for _, e0 in cands[:ncand]:
        s = sep23(e0, A)
        if s is None: continue
        u = up_get(e0, B, depth)
        if u is None: continue
        if s - u > best[0]: best = (s - u, e0, depth)
    if SEPIV1 and best[0] < 1: return (-INF, None, None)
    return best
def sepAny(B, A):
    s = sep23(B, A)
    f, e0 = form4(B, A)[:2]
    return max(s if s is not None else -INF, f), (s is not None and s >= f)
# ---------------- emission of the tables actually used (Up: keep min, Sep: keep max; each with its own justification)
UPT = {}; SEPT = {}; UPJ = {}; SEPJ = {}
def _put_sep(b, a, d, j):
    if (b, a) in SEPT and SEPT[(b, a)] >= d: return False
    SEPT[(b, a)] = d; SEPJ[(b, a)] = j; return True
def emit_sep23(s, T):
    stack = [(s, T)]
    while stack:
        s_, T_ = stack.pop()
        d = sep23(s_, T_)
        assert d is not None
        if s_ == T_:
            _put_sep(s_, T_, 0, ("refl",)); continue
        if (s_, T_) in SEPT and SEPT[(s_, T_)] >= d: continue
        v = el[T_][0]
        # recompute which form gives d (same as sep23)
        pp = prev[T_]
        pv = sep23(s_, pp) if pp is not None and leqP(s_, pp) and tm[pp] >= tm[s_] else None
        if pv is not None and pv + wlo(v, v) >= d:
            _put_sep(s_, T_, d, ("prev",)); stack.append((s_, pp)); continue
        chosen = []
        for alt in alts[T_]:
            bp = None
            for p in alt:
                if not leqP(s_, p) or tm[p] < tm[s_]: continue
                x = sep23(s_, p)
                if x is None: continue
                if bp is None or x + wlo(v, el[p][0]) > bp[0]: bp = (x + wlo(v, el[p][0]), p)
            assert bp is not None and bp[0] >= d, ("sep23 replay", s_, T_)
            chosen.append(bp[1])
        assert alts[T_]
        _put_sep(s_, T_, d, ("alts",))
        for p in chosen: stack.append((s_, p))
def emit_up(e0, e, depth):
    stack = [(e0, e, depth)]
    while stack:
        e0_, e_, dp = stack.pop()
        st = UPST[(e0_, dp)]; d = st["U"][e_]; j = st["J"][e_]
        if (e0_, e_) in UPT and UPT[(e0_, e_)] <= d: continue
        UPT[(e0_, e_)] = d; UPJ[(e0_, e_)] = j
        if j[0] == "eq": continue
        _, ai, tags, ptag = j
        items = list(zip(alts[e_][ai], tags)) + ([(prev[e_], ptag)] if ptag is not None else [])
        for p, tg in items:
            if tg[0] == "U": stack.append((e0_, p, dp))
            elif tg[0] == "S": emit_sep23(p, e0_)
            else:
                a = tg[1]; up_get(a, p, tg[2]); stack.append((a, p, tg[2])); emit_sep23(a, e0_)
def emit_sepq(B, A):
    """emit the entries behind sepAny(B, A)"""
    s = sep23(B, A); f, e0, dp = form4(B, A)
    if s is not None and s >= f: emit_sep23(B, A); return s
    assert e0 is not None
    emit_sep23(e0, A); emit_up(e0, B, dp)
    _put_sep(B, A, f, ("iv", e0)); return f
