#!/usr/bin/env python3
"""Shard C (UNTRUSTED): pairwise time-separation bounds for "c before b" (successor of tse.py's single-reference
bound, which is unbounded whenever an event waits on a concurrent older event).
Events and preds as in tse.py (necessity by zero-delay re-evaluation; sensitised or structural hops).
Event set E = ancestors (changed preds, previous toggle, older last-events of supports) of b and of the pseudo
event c' (= c fires, given its inputs at b's reference point), within the last W events before b.
Matrices per corner: H[z][x] >= T(x) - T(z) (upper), Lo[z][x] <= T(x) - T(z) (lower), H[z][z] = Lo[z][z] = 0.
Rules, iterated to a fixpoint:
  HI : H[z][x] <= max over (changed preds p, older support events q in E, prev toggle (+loop(x))) of H[z][p] + maxhop;
       not applied if a changed pred lies outside E (unbounded) or x is an env event (env delay unbounded);
  LO : Lo[z][x] >= max over NECESSARY changed preds p of Lo[z][p] + minhop; also >= min over all changed preds
       (when all are in E);
  reversal H[z][x] <= -Lo[x][z]; triangle (Floyd-Warshall, min-plus on H, max-plus on Lo).
Order c-before-b at scatter kappa (every hop: [(1-k) lo, (1+k) hi]) holds if
       slack = H[b][c'] + (1+k) loop(c)  < 0         (c's loop settles before b's output moves)
kappa* = largest k with slack < 0 (bisection, recomputed with scaled hops: not a ratio formula).
Also reported: slack2 = slack - (1-k) minhop(b -> c) (deadline = b's change reaching c's output).
usage: tse2.py net.json bnd.json huff.txt TRACE.txt ...   env: TSE_WINDOW (400), DETAIL=1"""
import sys, os, collections, math
import numpy as np
import tse
from tse import *
_LC = {}
_loop0 = loop
def loop(v):
    if v not in gate: return (0, 0)
    if v not in _LC: _LC[v] = _loop0(v)
    return _LC[v]
W2 = int(os.environ.get("TSE_WINDOW", "400"))
MODES = os.environ.get("TSE_MODES", "sens,struct").split(",")

def build(path):
    T = Trace(path)
    base = os.path.basename(path).replace(".log", "")
    cname, bname = base.split("__")[0], base.split("__")[1]
    C = nid[cname]; ib = len(T.ev) - 1
    while T.ev[ib]["move"] != len(T.moves) - 1 or T.ev[ib]["pos"] != T.ev[ib]["mstart"]: ib -= 1
    assert names[T.ev[ib]["node"]] == bname
    Rb = T.ev[ib]["pos"]
    assert T.excited(C, Rb), "c not excited before b"
    lo_i = max(0, ib - W2)
    P = {}
    def gp(i):
        if i not in P: P[i] = preds(T, i)
        return P[i]
    # pseudo event c'
    pprev = T.lastflip(C, Rb); lim = -1 if pprev is None else pprev
    cch = []; cset = []
    for u in ssupp(C):
        q = T.lastflip(u, Rb)
        if q is None: continue
        if q > lim: cch.append((T.byPos[q], False, u))
        else: cset.append(T.byPos[q])
    P["c"] = (cch, cset, T.byPos[pprev] if pprev is not None else None, True, Rb)
    E = set(); st = [ib, "c"]
    while st:
        x = st.pop()
        if x in E: continue
        if x != "c" and x < lo_i: continue
        E.add(x)
        ch, settled, prev, _, _ = gp(x)
        for (p, nec, u) in ch: st.append(p)
        for q in settled: st.append(q)
        if prev is not None: st.append(prev)
    order = sorted(e for e in E if e != "c") + ["c"]
    return T, C, ib, order, P

def hops_for(T, C, P, order, mode):
    """per x: list of (kind, p, lo4, hi4) with kind in ch/chN/set/prev; flags"""
    HOPm = {}; flags = collections.Counter(); R = {}
    Eset = set(order)
    def hop(p, x):
        key = (p, x)
        if key not in HOPm:
            tgt = C if x == "c" else T.ev[x]["node"]
            HOPm[key] = hop_paths(T, p, tgt, P[x][4], mode)
        return HOPm[key]
    for x in order:
        ch, settled, prev, base, Rx = P[x]
        node = C if x == "c" else T.ev[x]["node"]
        items = []; out_of_E = False
        for (p, nec, u) in ch:
            if p not in Eset: out_of_E = True; flags["changed pred outside window"] += 1; continue
            h = hop(p, x)
            if h is None: flags["changed pred with no %s path" % mode] += 1; continue
            items.append(("chN" if nec else "ch", p, h[0], h[1]))
        for q in settled:
            if q not in Eset: flags["older support event outside window (assumed settled)"] += 1; continue
            h = hop(q, x)
            if h is not None: items.append(("set", q, h[0], h[1]))
        if prev is not None:
            if prev in Eset:
                l = loop(node); items.append(("prev", prev, (0, 0, 0, 0), (0, l[0], 0, l[1])))
            else: flags["previous toggle outside window (assumed settled)"] += 1
        isenv = x != "c" and node in ENV
        R[x] = (items, out_of_E, isenv, base)
        if not base: flags["event not excited at its reference point"] += 1
    return R, flags

def solve(order, R, corner, kap, iters=8):
    n = len(order); ix = {x: i for i, x in enumerate(order)}
    H = np.full((n, n), np.inf); L = np.full((n, n), -np.inf)
    np.fill_diagonal(H, 0); np.fill_diagonal(L, 0)
    fl, fh = (0, 1) if corner == 0 else (2, 3)
    a, b = 1 - kap, 1 + kap
    prep = []
    for x in order:
        items, oo, isenv, base = R[x]
        j = ix[x]
        hc = [(ix[p], b * hi[fh]) for (k, p, lo, hi) in items]
        nc = [(ix[p], a * lo[fl]) for (k, p, lo, hi) in items if k == "chN"]
        ac = [(ix[p], a * lo[fl]) for (k, p, lo, hi) in items if k in ("ch", "chN")]
        doH = (not oo) and (not isenv) and len(hc) > 0
        doMin = (not oo) and len(ac) > 0
        prep.append((j, hc, nc, ac, doH, doMin))
    for it in range(iters):
        H0 = H.copy(); L0 = L.copy()
        for (j, hc, nc, ac, doH, doMin) in prep:
            if doH:
                col = np.max(np.stack([H[:, p] + d for p, d in hc]), axis=0)
                H[:, j] = np.minimum(H[:, j], col)
            cands = [L[:, p] + d for p, d in nc]
            if doMin: cands.append(np.min(np.stack([L[:, p] + d for p, d in ac]), axis=0))
            if cands:
                L[:, j] = np.maximum(L[:, j], np.max(np.stack(cands), axis=0))
        H = np.minimum(H, -L.T); L = np.maximum(L, -H.T)
        for k in range(n):
            H = np.minimum(H, H[:, k:k + 1] + H[k:k + 1, :])
            L = np.maximum(L, L[:, k:k + 1] + L[k:k + 1, :])
        H = np.minimum(H, -L.T); L = np.maximum(L, -H.T)
        if np.array_equal(H, H0) and np.array_equal(L, L0): break
    incons = bool(np.any(L > H + 1e-6))
    return H, L, ix, incons

def margins(T, C, ib, order, R, corner, kap, extra):
    H, L, ix, inc = solve(order, R, corner, kap)
    lc = loop(C)[corner]
    s = H[ix[ib], ix["c"]] + (1 + kap) * lc
    s2 = s - (1 - kap) * extra[corner] if extra is not None else s
    return s, s2, H, L, ix, inc

def analyse2(path):
    T, C, ib, order, P = build(path)
    res = {}
    for mode in MODES:
        R, flags = hops_for(T, C, P, order, mode)
        hb = hop_paths(T, ib, C, T.ev[ib]["pos"] + 1, mode)
        extra = (hb[0][0], hb[0][2]) if hb else None
        rc = {}
        for corner in (0, 1):
            s0, s20, H, L, ix, inc = margins(T, C, ib, order, R, corner, 0.0, extra)
            if not (s0 < 0):
                rc[corner] = dict(k=None if not np.isfinite(s0) else -0.0, s0=s0, s20=s20, inc=inc);
                # kappa* for slack2 anyway
            lo, hi = 0.0, 0.96
            if s0 < 0 and (mode == MODES[0] or os.environ.get("TSE_BISECT_ALL")):
                ok = lambda m: margins(T, C, ib, order, R, corner, m, extra)[0] < 0
                # bracket from the single-reference ratio at kappa 0, then refine to 0.01
                Hc = H[:, ix["c"]]; Lb = L[:, ix[ib]]; lcc = loop(C)[corner]
                with np.errstate(invalid="ignore", divide="ignore"):
                    kr = np.where(np.isfinite(Hc) & np.isfinite(Lb) & (Lb + Hc + lcc > 0), (Lb - Hc - lcc) / (Lb + Hc + lcc), -1)
                k0 = max(0.0, math.floor(float(np.max(kr)) * 100) / 100)
                if k0 > 0 and ok(k0):
                    lo = k0
                    if ok(k0 + 0.01):
                        hi = 0.96
                        while hi - lo > 0.01:
                            m = (lo + hi) / 2
                            if ok(m): lo = m
                            else: hi = m
                else:
                    hi = k0 if k0 > 0 else 0.96
                    while hi - lo > 0.01:
                        m = (lo + hi) / 2
                        if ok(m): lo = m
                        else: hi = m
                rc[corner] = dict(k=lo, s0=s0, s20=s20, inc=inc)
            elif s0 < 0:
                rc[corner] = dict(k=float("nan"), s0=s0, s20=s20, inc=inc)
            # decomposition at kappa 0: best reference A = argmin_A H[A][c'] - L[A][b]
            Hc = H[:, ix["c"]]; Lb = L[:, ix[ib]]
            with np.errstate(invalid="ignore"):
                sep = Hc - Lb
            sep = np.where(np.isfinite(Hc) & np.isfinite(Lb), sep, np.inf)
            ai = int(np.argmin(sep))
            rc[corner].update(A=order[ai], HA=Hc[ai], LA=Lb[ai], H=H, L=L, ix=ix)
        res[mode] = (rc, flags, R)
    return T, C, ib, order, P, res

def chain_detail(T, C, ib, order, R, rc, corner, mode):
    """greedy explanation: the LO chain A -> b (tight necessary preds) and the HI chain A -> c'"""
    H, L, ix, A = rc["H"], rc["L"], rc["ix"], rc["A"]
    fl, fh = (0, 1) if corner == 0 else (2, 3)
    nm = lambda x: (names[C] + "'") if x == "c" else "%s@%d" % (names[T.ev[x]["node"]], x)
    ia = ix[A]; out = []
    out.append("    reference A = %s; HI(A->c') = %.0f, LO(A->b) = %.0f, loop(c) = %d" % (nm(A), rc["HA"], rc["LA"], loop(C)[corner]))
    x = ib; seen = 0; out.append("    LO chain b <- ... <- A (necessary preds, min-sum hops):")
    while x != A and seen < 60:
        items = R[x][0]; best = None
        for (k, p, lo, hi) in items:
            if k == "chN":
                v = L[ia, ix[p]] + lo[fl]
                if best is None or v > best[0]: best = (v, p, lo[fl])
        if best is None or abs(best[0] - L[ia, ix[x]]) > 1e-6 and not np.isfinite(best[0]):
            out.append("      %-26s LO %8.0f  (via closure)" % (nm(x), L[ia, ix[x]])); break
        out.append("      %-26s LO %8.0f  <- hop %5d from %s" % (nm(x), L[ia, ix[x]], best[2], nm(best[1])))
        x = best[1]; seen += 1
    x = "c"; seen = 0; out.append("    HI chain c' <- ... <- A (argmax preds, max-sum hops):")
    while x != A and seen < 60:
        items = R[x][0]; best = None
        for (k, p, lo, hi) in items:
            v = H[ia, ix[p]] + hi[fh]
            if best is None or v > best[0]: best = (v, p, hi[fh], k)
        if best is None:
            out.append("      %-26s HI %8.0f  (via closure)" % (nm(x), H[ia, ix[x]])); break
        out.append("      %-26s HI %8.0f  <- %s hop %5d from %s (HI %s)" % (nm(x), H[ia, ix[x]], best[3], best[2], nm(best[1]), "%.0f" % H[ia, ix[best[1]]]))
        if not np.isfinite(H[ia, ix[best[1]]]) or H[ia, ix[best[1]]] <= 0:
            if best[1] != A: out.append("      (pred precedes A: HI <= %.0f via closure)" % H[ia, ix[best[1]]])
            break
        x = best[1]; seen += 1
    return "\n".join(out)

if __name__ == "__main__":
    allres = collections.defaultdict(list)
    for path in sys.argv[4:]:
        base = os.path.basename(path).replace(".log", "").replace(".txt", "")
        pair = "__".join(base.split("__")[:2])
        try:
            T, C, ib, order, P, res = analyse2(path)
        except Exception as ex:
            import traceback; traceback.print_exc()
            print("==", base, "ERROR", repr(ex), flush=True); continue
        row = {}
        parts = []
        for mode in MODES:
            rc, flags, R = res[mode]
            for corner in (0, 1):
                r = rc[corner]; row[(mode, corner)] = r["k"]
                parts.append("%s/%s k*=%s slack0=%.0f slack2=%.0f%s" % (mode, "fs"[corner], "%.3f" % r["k"] if r["k"] is not None else "unb",
                             r["s0"], r["s20"], " INCONS" if r["inc"] else ""))
        fl = dict(res[MODES[0]][1])
        import resource
        print("== %s rss=%dMB |E|=%d  %s  flags[%s] %s" % (base, resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024, len(order), "  ".join(parts), MODES[0], fl), flush=True)
        import json as _j
        js = dict(base=base, pair=pair, E=len(order), flags={m: dict(res[m][1]) for m in MODES})
        for mode in MODES:
            for corner in (0, 1):
                r = res[mode][0][corner]
                a = r.get("A")
                js["%s/%s" % (mode, "fs"[corner])] = dict(k=r["k"], s0=float(r["s0"]), s2=float(r["s20"]), inc=r["inc"],
                    A=(names[T.ev[a]["node"]] + "@%d" % a) if isinstance(a, int) else str(a), HA=float(r.get("HA", np.inf)), LA=float(r.get("LA", -np.inf)), loop=loop(C)[corner])
        print("JSON", _j.dumps(js), flush=True)
        if os.environ.get("DETAIL"):
            for mode in MODES[:1]:
                rc, flags, R = res[mode]
                for corner in (0, 1):
                    print("  [%s corner %s]" % (mode, "fs"[corner])); print(chain_detail(T, C, ib, order, R, rc[corner], corner, mode))
        allres[pair].append((row, base))
    print("\n# per pair: min over traces of kappa* (None = unbounded/negative at kappa 0)")
    for pair in sorted(allres):
        rows = allres[pair]
        cells = []
        for mode in MODES:
            for corner in (0, 1):
                xs = [r[(mode, corner)] for r, _ in rows]
                if any(x is None for x in xs): cells.append("%s/%s none(%d)" % (mode, "fs"[corner], sum(x is None for x in xs)))
                else:
                    m = min(xs); w = [b for r, b in rows if r[(mode, corner)] == m][0]
                    cells.append("%s/%s %.3f" % (mode, "fs"[corner], m))
        wb = min(rows, key=lambda rb: (rb[0][(MODES[0], 1)] if rb[0][(MODES[0], 1)] is not None else -9))[1]
        print("%-34s n=%-3d %s  worst=%s" % (pair, len(rows), "  ".join(cells), wb.split("__")[-1]))
