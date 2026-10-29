#!/usr/bin/env python3
"""C-8z2: a unit-delay run of the concrete gcd_hw network that is meant to satisfy EVERY
hypothesis of `gcd_hw_live_final` at once (H = 1).

Differences from 8t's `formal/tools/capwit/sim.py` run (which it imports, unmodified):
  * the a/b sources are FREE-RUNNING (`req := !ack` after one tick, for ever), as
    H_BOUNDED_DELAY' demands of every gate except `start`'s LUT;
  * `start` offers exactly one token (H_START_ONCE); after its token closes its LUT is
    excited for ever and never fires (allowed: H_BOUNDED_DELAY' exempts it, H_START_ENV
    only constrains it before its first offer);
  * the run continues past out0's close until every gate but `start`'s LUT is quiescent.

Untrusted: the Lean kernel re-checks everything (CapstoneLiveWit*). This script mirrors the
Lean gate lists (`gatesE`, same order as `gatesK ++ grantsK`) to
  * check the step property "excited at t => output = target at t+1" for every gate but
    start's (this is what makes BndG 1 / ArbUnc 1 hold),
  * find, for every t before out0's close, one excited gate (the H_NO_DEADLOCK' certificate).
Usage: python3 -I livesim.py a b [--emit]   (--emit writes the generated Lean data files)
"""
import os, sys, math
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "formal", "tools", "capwit"))
sys.path.insert(0, HERE)
import sim  # noqa: E402
from sim import ev, jval, sel2, selD, outs_of, NINT, Cel  # noqa: E402


def simulate(a, b, names, ops, tmax=100000):
    NC = len(names)
    prod = {}
    for n, o in enumerate(ops):
        for c in outs_of(o): prod[c] = n
    req = [False] * NC; ack = [False] * NC
    it = {n: [False] * NINT.get(o["k"], 0) for n, o in enumerate(ops)}
    latch = {o["o"]: 0 for o in ops if o["k"] == "link"}
    started = False
    srcv = lambda w: a if w == 0 else (b if w == 1 else 0)

    def dats():
        memo = {}
        def d(c):
            if c in memo: return memo[c]
            o = ops[prod[c]]; k = o["k"]
            if k in ("forkG", "forkH"): v = d(o["i"])
            elif k == "join": v = ev(o["e"], [jval(j, [d(i) for i in o["ins"]]) for j in o["js"]])
            elif k == "bjoin":
                vs = [d(i) for i in o["ins"]]; v = 2 * ev(o["ed"], vs) + ev(o["ec"], vs) % 2
            elif k == "steerC": v = 0
            elif k == "steerD": v = ev(o["fd"], [d(o["j"]) // 2])
            elif k == "mux": v = d(o["y"]) if sel2(d(o["c"])) else d(o["x"])
            elif k == "muxn": v = d(o["xs"][selD(d(o["c"]))])
            elif k == "amerge":
                g = it[prod[c]]; won = g[1] or ack[o["y"]]
                v = 2 * (d(o["y"]) if won else d(o["x"])) + (1 if won else 0)
            elif k == "link": v = d(o["i"]) if it[prod[c]][0] else latch[c]
            elif k == "src": v = srcv(o["which"])
            memo[c] = v
            return v
        return [d(c) for c in range(NC)]

    D = dats()
    trace = [(list(req), list(ack), {n: list(v) for n, v in it.items()}, D)]
    for t in range(tmax):
        nreq, nack = list(req), list(ack)
        nit = {n: list(v) for n, v in it.items()}
        for n, o in enumerate(ops):
            k = o["k"]; g = it[n]
            if k in ("forkG", "forkH"):
                for c in o["os"]: nreq[c] = req[o["i"]]
                nack[o["i"]] = Cel(ack[o["i"]], [ack[c] for c in o["os"]])
            elif k in ("join", "bjoin"):
                nreq[o["o"]] = Cel(req[o["o"]], [req[i] for i in o["ins"]])
                for i in o["ins"]: nack[i] = ack[o["o"]]
            elif k in ("steerC", "steerD"):
                j = o["j"]; s = sel2(D[j])
                nreq[o["t"]] = req[j] and s; nreq[o["f"]] = req[j] and not s
                nack[j] = ack[o["t"]] or ack[o["f"]]
            elif k == "mux":
                c, x, y, z = o["c"], o["x"], o["y"], o["z"]; s = sel2(D[c])
                nit[n][0] = Cel(g[0], [req[x], req[c] and not s])
                nit[n][1] = Cel(g[1], [req[y], req[c] and s])
                nreq[z] = g[0] or g[1]
                nack[x] = Cel(ack[x], [g[0], ack[z]]); nack[y] = Cel(ack[y], [g[1], ack[z]])
                nack[c] = ack[z]
            elif k == "muxn":
                c, z = o["c"], o["z"]; s = selD(D[c])
                for m in range(3): nit[n][m] = Cel(g[m], [req[o["xs"][m]], req[c] and s == m])
                nreq[z] = g[0] or g[1] or g[2]
                for m in range(3):
                    x = o["xs"][m]; nack[x] = Cel(ack[x], [g[m], ack[z]])
                nack[c] = ack[z]
            elif k == "amerge":
                x, y, z = o["x"], o["y"], o["z"]; g1, g2 = g
                if not g1 and not g2 and req[x] and req[y] and not ack[z]:
                    raise RuntimeError(f"contested arbiter op {n} at {t}")
                ng1 = req[x] if g1 else (req[x] and not g2 and not ack[z])
                ng2 = req[y] if g2 else (req[y] and not g1 and not ack[z])
                nit[n] = [ng1, ng2]
                nreq[z] = (g1 or g2) if ((g1 or g2) == False or (not ack[x] and not ack[y])) else req[z]
                nack[x] = Cel(ack[x], [g1, ack[z]]); nack[y] = Cel(ack[y], [g2, ack[z]])
            elif k == "link":
                i, oo = o["i"], o["o"]; c = g[0]; r, qq = req[i], ack[oo]
                nit[n][0] = (r and not qq) or (c and (r or not qq))
                nack[i] = c; nreq[oo] = c
            elif k == "src":
                z = o["z"]
                if o["which"] == 2 and started and not req[z]: pass   # start: one offer only
                else: nreq[z] = not ack[z]
            elif k == "sink":
                nack[o["i"]] = req[o["i"]]
        if not req[2] and nreq[2]: started = True
        changed = (nreq != req) or (nack != ack) or (nit != it)
        req, ack, it = nreq, nack, nit
        for n, o in enumerate(ops):
            if o["k"] == "link": latch[o["o"]] = D[o["o"]]
        D2 = dats()
        for n, o in enumerate(ops):
            if o["k"] == "link": latch[o["o"]] = D2[o["o"]]
        changed = changed or (D2 != D)
        D = D2
        trace.append((list(req), list(ack), {n: list(v) for n, v in it.items()}, D))
        if not changed:
            return trace
    raise RuntimeError("no quiescence")


# ---- gate lists, same order as Lean `gatesK p k ++ grantsK p k` --------------------------
# a gate: (out, excT, excF) with out(S) and exc*(S) functions of a state accessor S
def gates(n, o):
    k = o["k"]
    G = []
    if k in ("forkG", "forkH"):
        i = o["i"]
        for c in o["os"]:
            G.append((lambda S, c=c: S.r(c), lambda S: S.r(i), lambda S: not S.r(i)))
        G.append((lambda S: S.a(i), lambda S: all(S.a(c) for c in o["os"]),
                  lambda S: all(not S.a(c) for c in o["os"])))
    elif k in ("join", "bjoin"):
        oo = o["o"]
        G.append((lambda S: S.r(oo), lambda S: all(S.r(i) for i in o["ins"]),
                  lambda S: all(not S.r(i) for i in o["ins"])))
        for i in o["ins"]:
            G.append((lambda S, i=i: S.a(i), lambda S: S.a(oo), lambda S: not S.a(oo)))
    elif k in ("steerC", "steerD"):
        j, tc, fc = o["j"], o["t"], o["f"]
        G.append((lambda S: S.r(tc), lambda S: S.r(j) and sel2(S.d(j)), lambda S: not (S.r(j) and sel2(S.d(j)))))
        G.append((lambda S: S.r(fc), lambda S: S.r(j) and not sel2(S.d(j)), lambda S: not (S.r(j) and not sel2(S.d(j)))))
        G.append((lambda S: S.a(j), lambda S: S.a(tc) or S.a(fc), lambda S: not (S.a(tc) or S.a(fc))))
    elif k == "mux":
        c, x, y, z = o["c"], o["x"], o["y"], o["z"]
        G.append((lambda S: S.i(n, 0), lambda S: S.r(x) and (S.r(c) and not sel2(S.d(c))),
                  lambda S: (not S.r(x)) and not (S.r(c) and not sel2(S.d(c)))))
        G.append((lambda S: S.i(n, 1), lambda S: S.r(y) and (S.r(c) and sel2(S.d(c))),
                  lambda S: (not S.r(y)) and not (S.r(c) and sel2(S.d(c)))))
        G.append((lambda S: S.r(z), lambda S: S.i(n, 0) or S.i(n, 1), lambda S: not (S.i(n, 0) or S.i(n, 1))))
        G.append((lambda S: S.a(x), lambda S: S.i(n, 0) and S.a(z), lambda S: not S.i(n, 0) and not S.a(z)))
        G.append((lambda S: S.a(y), lambda S: S.i(n, 1) and S.a(z), lambda S: not S.i(n, 1) and not S.a(z)))
        G.append((lambda S: S.a(c), lambda S: S.a(z), lambda S: not S.a(z)))
    elif k == "muxn":
        c, z, xs = o["c"], o["z"], o["xs"]
        for m in range(3):
            G.append((lambda S, m=m: S.i(n, m), lambda S, m=m: S.r(xs[m]) and (S.r(c) and selD(S.d(c)) == m),
                      lambda S, m=m: (not S.r(xs[m])) and not (S.r(c) and selD(S.d(c)) == m)))
        G.append((lambda S: S.r(z), lambda S: S.i(n, 0) or S.i(n, 1) or S.i(n, 2),
                  lambda S: not (S.i(n, 0) or S.i(n, 1) or S.i(n, 2))))
        for m in range(3):
            G.append((lambda S, m=m: S.a(xs[m]), lambda S, m=m: S.i(n, m) and S.a(z),
                      lambda S, m=m: not S.i(n, m) and not S.a(z)))
        G.append((lambda S: S.a(c), lambda S: S.a(z), lambda S: not S.a(z)))
    elif k == "amerge":
        x, y, z = o["x"], o["y"], o["z"]
        G.append((lambda S: S.r(z), lambda S: (S.i(n, 0) or S.i(n, 1)) and not S.a(x) and not S.a(y),
                  lambda S: not (S.i(n, 0) or S.i(n, 1))))
        G.append((lambda S: S.a(x), lambda S: S.i(n, 0) and S.a(z), lambda S: not S.i(n, 0) and not S.a(z)))
        G.append((lambda S: S.a(y), lambda S: S.i(n, 1) and S.a(z), lambda S: not S.i(n, 1) and not S.a(z)))
        G.append((lambda S: S.i(n, 0), lambda S: S.r(x) and not S.i(n, 1) and not S.a(z), lambda S: not S.r(x)))
        G.append((lambda S: S.i(n, 1), lambda S: S.r(y) and not S.i(n, 0) and not S.a(z), lambda S: not S.r(y)))
    elif k == "link":
        i, oo = o["i"], o["o"]
        ctl = lambda S: (S.r(i) and not S.a(oo)) or (S.i(n, 0) and (S.r(i) or not S.a(oo)))
        G.append((lambda S: S.i(n, 0), ctl, lambda S: not ctl(S)))
        G.append((lambda S: S.a(i), lambda S: S.i(n, 0), lambda S: not S.i(n, 0)))
        G.append((lambda S: S.r(oo), lambda S: S.i(n, 0), lambda S: not S.i(n, 0)))
    elif k == "src":
        z = o["z"]
        G.append((lambda S: S.r(z), lambda S: not S.a(z), lambda S: S.a(z)))
    elif k == "sink":
        i = o["i"]
        G.append((lambda S: S.a(i), lambda S: S.r(i), lambda S: not S.r(i)))
    return G


class St:
    def __init__(self, tr, t):
        s = tr[min(t, len(tr) - 1)]
        self.R, self.A, self.I, self.D = s
    def r(self, c): return self.R[c]
    def a(self, c): return self.A[c]
    def i(self, n, k): return self.I[n][k]
    def d(self, c): return self.D[c]


def analyse(a, b, names, ops, out0, tr):
    T = len(tr) - 1
    errs, falls = sim.check(a, b, names, ops, out0, tr)
    prod = {}
    for n, o in enumerate(ops):
        for c in outs_of(o): prod[c] = n
    pstart = prod[2]
    GL = [gates(n, o) for n, o in enumerate(ops)]
    # step property for every gate but start's, every t (the run is constant after T)
    sp_bad = []
    for n, G in enumerate(GL):
        if n == pstart: continue
        for j, (out, eT, eF) in enumerate(G):
            for t in range(T + 2):
                S0, S1 = St(tr, t), St(tr, t + 1)
                if eT(S0) and not out(S1): sp_bad.append((n, j, t, True))
                if eF(S0) and out(S1): sp_bad.append((n, j, t, False))
    close = falls[0] + 1 if falls else None   # first t with cnt fallB = 1 ... see note
    cert = []
    for t in range(falls[0] + 1 if falls else 0):
        S = St(tr, t); found = None
        for n, G in enumerate(GL):
            if n == pstart: continue
            for j, (out, eT, eF) in enumerate(G):
                if eT(S) and not out(S): found = (n, j, True); break
                if eF(S) and out(S): found = (n, j, False); break
            if found: break
        cert.append(found)
    return errs, falls, sp_bad, cert, pstart


def main():
    a = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    b = int(sys.argv[2]) if len(sys.argv) > 2 else 18
    names, ops, out0 = sim.load_net()
    tr = simulate(a, b, names, ops)
    T = len(tr) - 1
    errs, falls, sp_bad, cert, pstart = analyse(a, b, names, ops, out0, tr)
    nt = sum(len(sim.toggles([s[0][c] for s in tr])) + len(sim.toggles([s[1][c] for s in tr]))
             for c in range(len(names)))
    print(f"a={a} b={b}: quiescent (but start) after {T} ticks; {nt} req/ack toggles; start prod op {pstart}")
    print(f"out0 ack falls at {falls}, values {[tr[e][3][out0] for e in falls]}, gcd {math.gcd(a, b)}")
    print(f"model violations: {len(errs)} {errs[:5]}")
    print(f"step-property violations: {len(sp_bad)} {sp_bad[:5]}")
    print(f"no-deadlock certificate: {len(cert)} ticks, missing {sum(1 for c in cert if c is None)}")
    rises = [sum(1 for t in range(T) if not tr[t][0][c] and tr[t + 1][0][c]) for c in range(len(names))]
    print(f"max offers on a channel: {max(rises)} ({names[rises.index(max(rises))]}); a,b src offers {rises[0]}, {rises[1]}")
    if "--emit" in sys.argv:
        import emit
        emit.emit(a, b, names, ops, out0, tr, falls, cert)
    ok = not errs and not sp_bad and falls and all(c is not None for c in cert) and \
        tr[falls[0]][3][out0] == math.gcd(a, b)
    print("OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
