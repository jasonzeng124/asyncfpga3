#!/usr/bin/env python3
"""Probe Bwit2 (shard B): bsim.py with bd_mux gate-modelled too (j0 j1 uor udly[2] uxa uya).

Original doc of bsim.py follows.
Probe Bwit (shard B): a GATE-TIMED run of gcd_hw for the driver-bound network (untrusted).

Reads C's network and simulator (formal/tools/capwit/sim.py, read-only, imported). Same run
as C's unit-delay sim EXCEPT that every operator B gate-models (FiniteNetBound.FTied: fork
N=2..4 acknowledge C-element, 2-input join request C-element, steer branch LUTs, steer
acknowledge OR) has an explicit node: node(t+1) = excitation(t) (LUT delay 1), and the
channel signal it drives = node one tick later (wire 1), i.e. 2 ticks channel to channel, as
B's LUT + wire. Links are already LUT 1 + wire 1 in C's sim (c, then ack/req). Then:
 * C's own checker (sim.check: every Cell field, Held, start once, out0 value) on the run;
 * B wiring: for every tied pin whose driver the netlist names (FiniteNetBound.reqSrc /
   ackSrc, re-implemented here), the pin trace equals the driver's node delayed by a constant
   w >= 1 (reported per pin; fork outputs / join input acks get longer w).
usage: python3 -B bsim.py [a b]
"""
import os, sys, math
HERE = os.path.dirname(os.path.abspath(__file__))
CAP = os.path.abspath(os.path.join(HERE, "..", "..", "tools", "capwit"))
sys.path.insert(0, CAP)
import sim as S  # noqa: E402

def tiedfork(o): return o["k"] in ("forkG", "forkH") and 2 <= len(o["os"]) <= 4
MD = 6   # C's mux j_b := B's j_b node delayed MD ticks
def tiedmux(o): return o["k"] == "mux"
def tiedjoin(o): return o["k"] in ("join", "bjoin") and len(o["ins"]) == 2
def steer(o): return o["k"] in ("steerC", "steerD")

def simulate(a, b, names, ops, tmax=100000):
    NC = len(names)
    prod = {}
    for n, o in enumerate(ops):
        for c in S.outs_of(o): prod[c] = n
    req = [False] * NC; ack = [False] * NC
    it = {n: [False] * S.NINT.get(o["k"], 0) for n, o in enumerate(ops)}
    nd = {}  # B nodes of tied ops: fork/join: [x]; steer: [sbT, sbF, ao]
    for n, o in enumerate(ops):
        if tiedfork(o) or tiedjoin(o): nd[n] = [False]
        if steer(o): nd[n] = [False, False, False]
        if o["k"] == "mux": nd[n] = [False] * 7   # j0 j1 or d0 d1 xa ya
    jh = {n: [] for n, o in enumerate(ops) if o["k"] == "mux"}   # history of B's j nodes
    ndp = {n: list(v) for n, v in nd.items()}
    latch = {o["o"]: 0 for o in ops if o["k"] == "link"}
    srcdone = {n: False for n, o in enumerate(ops) if o["k"] == "src"}
    srcleft = {n: 1 for n, o in enumerate(ops) if o["k"] == "src"}
    srcv = lambda w: a if w == 0 else (b if w == 1 else 0)
    def dats():
        memo = {}
        def d(c):
            if c in memo: return memo[c]
            o = ops[prod[c]]; k = o["k"]
            if k in ("forkG", "forkH"): v = d(o["i"])
            elif k == "join": v = S.ev(o["e"], [S.jval(j, [d(i) for i in o["ins"]]) for j in o["js"]])
            elif k == "bjoin":
                vs = [d(i) for i in o["ins"]]; v = 2 * S.ev(o["ed"], vs) + S.ev(o["ec"], vs) % 2
            elif k == "steerC": v = 0
            elif k == "steerD": v = S.ev(o["fd"], [d(o["j"]) // 2])
            elif k == "mux": v = d(o["y"]) if S.sel2(d(o["c"])) else d(o["x"])
            elif k == "muxn": v = d(o["xs"][S.selD(d(o["c"]))])
            elif k == "amerge":
                g = it[prod[c]]; won = g[1] or ack[o["y"]]
                v = 2 * (d(o["y"]) if won else d(o["x"])) + (1 if won else 0)
            elif k == "link": v = d(o["i"]) if it[prod[c]][0] else latch[c]
            elif k == "src": v = srcv(o["which"])
            memo[c] = v; return v
        return [d(c) for c in range(NC)]
    trace = []
    D = dats()
    snap = lambda: (list(req), list(ack), {n: list(v) for n, v in it.items()}, D, {n: list(v) for n, v in nd.items()})
    trace.append(snap())
    for t in range(tmax):
        nreq, nack = list(req), list(ack)
        nit = {n: list(v) for n, v in it.items()}
        nnd = {n: list(v) for n, v in nd.items()}
        for n, o in enumerate(ops):
            k = o["k"]; g = it[n]
            if k in ("forkG", "forkH"):
                for c in o["os"]: nreq[c] = req[o["i"]]
                if tiedfork(o):
                    nnd[n][0] = S.Cel(nd[n][0], [ack[c] for c in o["os"]]); nack[o["i"]] = nd[n][0]
                else: nack[o["i"]] = S.Cel(ack[o["i"]], [ack[c] for c in o["os"]])
            elif k in ("join", "bjoin"):
                if tiedjoin(o):
                    nnd[n][0] = S.Cel(nd[n][0], [req[i] for i in o["ins"]]); nreq[o["o"]] = nd[n][0]
                else: nreq[o["o"]] = S.Cel(req[o["o"]], [req[i] for i in o["ins"]])
                for i in o["ins"]: nack[i] = ack[o["o"]]
            elif steer(o):
                j = o["j"]; s = S.sel2(D[j])
                nnd[n][0] = req[j] and s; nnd[n][1] = req[j] and not s
                nnd[n][2] = ack[o["t"]] or ack[o["f"]]
                nreq[o["t"]] = nd[n][0]; nreq[o["f"]] = nd[n][1]; nack[j] = nd[n][2]
            elif k == "mux":
                c, x, y, z = o["c"], o["x"], o["y"], o["z"]; s = S.sel2(D[c])
                q = nd[n]; p = ndp[n]   # p: the nodes one tick earlier = internal pins (wire 1)
                nnd[n][0] = S.Cel(q[0], [req[x], req[c] and not s])
                nnd[n][1] = S.Cel(q[1], [req[y], req[c] and s])
                nnd[n][2] = p[0] or p[1]
                nnd[n][3] = p[2]
                nnd[n][4] = p[3]
                nnd[n][5] = S.Cel(q[5], [p[0], ack[z]])
                nnd[n][6] = S.Cel(q[6], [p[1], ack[z]])
                nreq[z] = q[4]
                nack[x] = q[5]; nack[y] = q[6]
                nack[c] = ack[z]
                hist = jh[n]
                hist.append((nnd[n][0], nnd[n][1]))
                old = hist[-MD - 1] if len(hist) > MD else (False, False)
                nit[n][0], nit[n][1] = old
            elif k == "muxn":
                c, z = o["c"], o["z"]; s = S.selD(D[c])
                for m in range(3): nit[n][m] = S.Cel(g[m], [req[o["xs"][m]], req[c] and s == m])
                nreq[z] = g[0] or g[1] or g[2]
                for m in range(3):
                    x = o["xs"][m]; nack[x] = S.Cel(ack[x], [g[m], ack[z]])
                nack[c] = ack[z]
            elif k == "amerge":
                x, y, z = o["x"], o["y"], o["z"]; g1, g2 = g
                ng1 = req[x] if g1 else (req[x] and not g2 and not ack[z])
                ng2 = req[y] if g2 else (req[y] and not g1 and not ack[z] and not ng1)
                nit[n] = [ng1, ng2]; nreq[z] = g1 or g2
                nack[x] = S.Cel(ack[x], [g1, ack[z]]); nack[y] = S.Cel(ack[y], [g2, ack[z]])
            elif k == "link":
                i, oo = o["i"], o["o"]; c = g[0]; r, q = req[i], ack[oo]
                nit[n][0] = (r and not q) or (c and (r or not q)); nack[i] = c; nreq[oo] = c
            elif k == "src":
                z = o["z"]
                if req[z] or not srcdone[n]: nreq[z] = not ack[z]
            elif k == "sink": nack[o["i"]] = req[o["i"]]
        for n, o in enumerate(ops):
            if o["k"] == "src" and not req[o["z"]] and nreq[o["z"]]:
                srcleft[n] -= 1; srcdone[n] = srcleft[n] == 0
        changed = (nreq != req) or (nack != ack) or (nit != it) or (nnd != nd) or (ndp != nd)
        ndp = {n: list(v) for n, v in nd.items()}
        req, ack, it, nd = nreq, nack, nit, nnd
        D2 = dats()
        for n, o in enumerate(ops):
            if o["k"] == "link": latch[o["o"]] = D2[o["o"]]
        changed = changed or (D2 != D); D = D2
        trace.append(snap())
        if not changed: return trace
    raise RuntimeError("no quiescence")

# ---- FiniteNetBound.reqSrc / ackSrc, re-implemented (fuel 16) ----
def reqSrc(F, c, ops, prod):
    if F == 0: return None
    n = prod[c]; o = ops[n]; k = o["k"]
    if k == "link": return ("lk", n)
    if steer(o): return ("sb", n, c == o["t"])
    if k in ("join", "bjoin"):
        if len(o["ins"]) == 2: return ("jr", n)
        if len(o["ins"]) == 1: return reqSrc(F - 1, o["ins"][0], ops, prod)   # a 1-input join is a wire
        return None
    if k in ("forkG", "forkH"): return reqSrc(F - 1, o["i"], ops, prod) if tiedfork(o) else None
    if k == "mux": return ("md", n, 1)
    return None
def ackSrc(F, c, ops, cons):
    if F == 0: return None
    n = cons[c]; o = ops[n]; k = o["k"]
    if k == "link": return ("lk", n)
    if steer(o): return ("ao", n)
    if k in ("forkG", "forkH"): return ("fa", n) if tiedfork(o) else None
    if k in ("join", "bjoin"): return ackSrc(F - 1, o["o"], ops, cons) if len(o["ins"]) in (1, 2) else None
    if k == "mux":
        if c == o["c"]: return ackSrc(F - 1, o["z"], ops, cons)
        return ("ma", n, c == o["y"])
    return None

NEG = 1 if "--neg" in sys.argv else 0

def main():
    sys.argv = [x for x in sys.argv if x != "--neg"]
    a = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    b = int(sys.argv[2]) if len(sys.argv) > 2 else 18
    names, ops, out0 = S.load_net()
    tr = simulate(a, b, names, ops)
    errs, falls = S.check(a, b, names, ops, out0, [x[:4] for x in tr])
    T = len(tr)
    print(f"a={a} b={b}: quiescent after {T-1} ticks; out0 closes at {falls} value {[tr[e][3][out0] for e in falls]} gcd {math.gcd(a,b)}")
    print(f"C checker: {len(errs)} violations", errs[:10])
    prod, cons = {}, {}
    for n, o in enumerate(ops):
        for c in S.outs_of(o): prod[c] = n
        for c in S.ins_of(o): cons[c] = n
    def node(d, t):
        t = min(max(t, 0), T - 1); x = tr[t]
        if d[0] == "lk": return x[2][d[1]][0]
        if d[0] in ("fa", "jr"): return x[4][d[1]][0]
        if d[0] == "sb": return x[4][d[1]][(0 if d[2] else 1) ^ NEG]
        if d[0] == "ao": return x[4][d[1]][2]
        if d[0] == "md": return x[4][d[1]][3 + d[2]]
        if d[0] == "ma": return x[4][d[1]][6 if d[2] else 5]
    def sig(c, side, t):
        t = min(t, T - 1); return tr[t][0 if side == "r" else 1][c]
    # tied pins: (reader, channel, side)
    pins = []
    for n, o in enumerate(ops):
        k = o["k"]
        if k == "link": pins += [(n, o["i"], "r"), (n, o["o"], "a")]
        if tiedfork(o): pins += [(n, c, "a") for c in o["os"]]
        if tiedjoin(o): pins += [(n, c, "r") for c in o["ins"]]
        if steer(o): pins += [(n, o["j"], "r"), (n, o["t"], "a"), (n, o["f"], "a")]
        if tiedmux(o): pins += [(n, o["x"], "r"), (n, o["y"], "r"), (n, o["c"], "r"), (n, o["z"], "a")]
    bad = []; ws = {}; bound = 0
    for (n, c, side) in pins:
        d = reqSrc(16, c, ops, prod) if side == "r" else ackSrc(16, c, ops, cons)
        if d is None: continue
        bound += 1
        ok = [w for w in range(1, 8) if all(sig(c, side, t) == (node(d, t - w) if t >= w else False) for t in range(T + 2))]
        if not ok: bad.append((names[c], side, d))
        else: ws[ok[0]] = ws.get(ok[0], 0) + 1
    both = sum(1 for o in ops if o['k'] == 'link' and reqSrc(16, o['i'], ops, prod) and ackSrc(16, o['o'], ops, cons))
    print('links bound both sides:', both)
    print(f"bound tied pins: {bound}; wire delays found {ws}; NOT a delayed copy of the bound driver: {len(bad)}", bad[:10])
    return 0 if not errs and not bad else 1

if __name__ == "__main__":
    sys.exit(main())
