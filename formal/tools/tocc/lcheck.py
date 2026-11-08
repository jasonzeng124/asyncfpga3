#!/usr/bin/env python3
"""Shard C helper (UNTRUSTED): OccNet.LCheck / TimedOccX.LCheckX at every exact node, by enumerating every count
vector over D v respecting the pairwise bounds L (diagonal excluded) and n u <= len u.
Data inputs: X (all values) unless a guard (list per (v, z): (st, en, val)) is on; guards come from guards.py.
Returns per node: number of vectors, failures by kind, and failing vectors (capped)."""
import sys, collections
sys.path.insert(0, "/tmp/claude-0/tocc")
from cert import L
from classify import lut

def Dof(K, v):
    C = K["C"]; EX = C["EXACT"]
    if v in K["envnode"]:
        from cert import ENVREAD
        return [v] + [C["bs"][k] for k in ENVREAD[K["envnode"][v]]]
    D = [v]
    for p in C["live"][v]:
        w = p["src"]
        if w in EX and w not in D: D.append(w)
    for k in range(len(K["ev"][v])):
        for (w, i) in K["causes"][(v, k)]:
            if w not in D: D.append(w)
    return D

def env_en(K, v, s, n):
    C = K["C"]; bs = C["bs"]; kind = K["envnode"][v]
    if kind == "rst": return s[v]
    if kind == "pend_ack": return s[v] != s[bs["req"]]
    if kind == "out0_ack": return s[v] != s[bs["out0_req"]]
    if kind == "req":
        acks = [s[bs[k]] for k in ("a_ack", "b_ack", "start_ack")]
        if not s[v]: return (not any(acks)) and n[v] == 0     # one pair: phase = own count (NOT a state rule)
        return all(acks)

def check_node(K, v, guards=None, cap=50):
    C = K["C"]; gates = C["gates"]; ev = K["ev"]; s0 = K["s0"]; EX = C["EXACT"]
    D = Dof(K, v); lens = [len(ev[u]) for u in D]
    # precompute bound table: B[i][k][j] = L(D[i], k, D[j])
    Bt = [[[L(K, D[i], k, D[j]) for j in range(len(D))] for k in range(lens[i])] for i in range(len(D))]
    isenv = v in K["envnode"]
    if not isenv:
        g = gates[v]; pins = g["pins"]
        pin_kind = []
        for p in pins:
            w = p["src"]
            if not p["live"]: pin_kind.append(("c", K["valat"](w, K["t0"])))
            elif w in EX: pin_kind.append(("x", D.index(w)))
            elif w in C["const"]: pin_kind.append(("c", K["valat"](w, K["t0"])))
            else: pin_kind.append(("d", w))
        dpins = sorted(set(x[1] for x in pin_kind if x[0] == "d"))
    lenv = lens[0]
    causes_v = [[(D.index(w), i) for (w, i) in K["causes"][(v, k)]] for k in range(lenv)]
    nvec = 0; fails = collections.Counter(); ex = []
    n = [0] * len(D)
    m = len(D)
    def ok_partial(i):
        # new coordinate i: check bounds between i and every j < i both directions
        ni = n[i]
        if ni > 0:
            row = Bt[i][ni - 1]
            for j in range(i):
                if row[j] > n[j]: return False
        for j in range(i):
            nj = n[j]
            if nj > 0 and Bt[j][nj - 1][i] > ni: return False
        return True
    def evaluate():
        s = {D[j]: s0[D[j]] ^ (n[j] & 1) for j in range(m)}
        if isenv:
            exc = {bool(env_en(K, v, s, dict(zip(D, n))))}
        else:
            exc = set()
            dv = {}
            if guards:
                for z in dpins:
                    for (st, en, val) in guards.get((v, z), ()):
                        on = (st is None or st[1] < n[D.index(st[0])]) and (en is None or n[D.index(en[0])] <= en[1])
                        if on: dv[z] = val; break
            free = [z for z in dpins if z not in dv]
            for mask in range(1 << len(free)):
                bb = dict(dv)
                for q, z in enumerate(free): bb[z] = bool(mask >> q & 1)
                bits = [(pk[1] if pk[0] == "c" else (s[D[pk[1]]] if pk[0] == "x" else bb[pk[1]])) for pk in pin_kind]
                exc.add(bool(lut(g["init"], g["k"], bits)) != s[v])
                if len(exc) == 2: break
        nv = n[0]
        enab = nv < lenv and all(i < n[j] for (j, i) in causes_v[nv])
        if len(exc) == 2: kind = "X"
        elif exc == {True} and not enab: kind = "EnE"
        elif exc == {False} and enab: kind = "NxE"
        else: return
        fails[kind] += 1
        if len(ex) < cap: ex.append((kind, tuple(n)))
    def rec(i):
        nonlocal nvec
        if i == m:
            nvec += 1; evaluate(); return
        for x in range(lens[i] + 1):
            n[i] = x
            if ok_partial(i): rec(i + 1)
        n[i] = 0
    rec(0)
    return dict(D=D, lens=lens, nvec=nvec, fails=fails, ex=ex)

if __name__ == "__main__":
    import time, pickle
    from cert import build
    c = int(sys.argv[1]); mode = sys.argv[2] if len(sys.argv) > 2 else "all"
    t = time.time(); K = build(c, mode)
    res = {}; tot = collections.Counter(); nv = 0; maxD = 0
    for v in sorted(K["C"]["EXACT"]):
        r = check_node(K, v); res[v] = r; nv += r["nvec"]; tot.update(r["fails"]); maxD = max(maxD, len(r["D"]))
    bad = [v for v in res if res[v]["fails"]]
    print("c=%d mode=%s: nodes %d, vectors %d, max|D| %d, failing nodes %d, fails %s (%.0fs)" % (
        c, mode, len(res), nv, maxD, len(bad), dict(tot), time.time() - t))
    pickle.dump({v: dict(r, fails=dict(r["fails"])) for v, r in res.items()}, open("/tmp/claude-0/tocc/lc_c%d_%s.pkl" % (c, mode), "wb"))
