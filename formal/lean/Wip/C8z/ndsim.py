#!/usr/bin/env python3
"""C-8z: empirical check of H_NO_DEADLOCK' and H_OFFER_BOUND_NS on gcd_hw's network.

Random-delay runs of the same gate models as formal/tools/capwit/sim.py (8t), with two
changes: the a/b sources are FREE-RUNNING (bd_src, req = !ack, as H_BOUNDED_DELAY' demands),
`start` offers once; and every excited gate fires at a tick with probability q (q = 1:
8t's synchronous unit-delay run). Up to the first out0 close it records:
  * whether some gate other than start's LUT is excited at every tick (H_NO_DEADLOCK'),
  * per-channel request rises (offers); spine / non-spine maxima (H_OFFER_BOUND_NS's M),
  * the number of projected-state changes (the N of firing_bound).
Evidence only: a few schedules per vector; proves nothing.
Usage: python3 -I ndsim.py [nvec] [seeds]
"""
import os, sys, random
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "formal", "tools", "capwit"))
import sim  # noqa: E402  (8t's simulator: net loader, data evaluation helpers)
from sim import ev, jval, sel2, selD, outs_of, NINT, Cel  # noqa: E402
import re


def spine():
    txt = open(os.path.join(ROOT, "formal", "lean", "Formal", "Net", "CapstoneCutSpine.lean")).read()
    body = re.search(r"def spL : List Bool := \[(.*?)\]", txt, re.S).group(1)
    return [x.strip() == "true" for x in body.split(",")]


def run(a, b, names, ops, out0, q, rng, tmax=200000):
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
    rises = [0] * NC
    changes = 0
    for t in range(tmax):
        nreq, nack = list(req), list(ack)
        nit = {n: list(v) for n, v in it.items()}
        for n, o in enumerate(ops):          # full excitation (every gate fires)
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
                ng1 = req[x] if g1 else (req[x] and not g2 and not ack[z])
                ng2 = req[y] if g2 else (req[y] and not g1 and not ack[z] and not ng1)
                nit[n] = [ng1, ng2]
                if not g1 and not g2 and req[x] and req[y] and not ack[z]:
                    raise RuntimeError(f"contested arbiter op {n} at {t}")
                nreq[z] = g1 or g2
                nack[x] = Cel(ack[x], [g1, ack[z]]); nack[y] = Cel(ack[y], [g2, ack[z]])
            elif k == "link":
                i, oo = o["i"], o["o"]; c = g[0]; r, qq = req[i], ack[oo]
                nit[n][0] = (r and not qq) or (c and (r or not qq))
                nack[i] = c; nreq[oo] = c
            elif k == "src":
                z = o["z"]
                if o["which"] == 2 and started and not req[z]: pass   # start: once
                else: nreq[z] = not ack[z]
            elif k == "sink":
                nack[o["i"]] = req[o["i"]]
        excited = (nreq != req) or (nack != ack) or (nit != it)
        if not excited:
            return dict(ok=False, why=f"quiescent at {t} before out0 close", t=t)
        # random subset fires (each output independently, prob q)
        f = lambda old, new: new if (old != new and rng.random() < q) else old
        nreq = [f(o_, n_) for o_, n_ in zip(req, nreq)]
        nack = [f(o_, n_) for o_, n_ in zip(ack, nack)]
        nit = {n: [f(o_, n_) for o_, n_ in zip(it[n], nit[n])] for n in it}
        for n, o in enumerate(ops):  # arbiter exclusion kept (H_ARB_EXCL)
            if o["k"] == "amerge" and nit[n][0] and nit[n][1]:
                nit[n][1] = it[n][1]; nit[n][0] = it[n][0] if not it[n][0] else nit[n][0]
                if nit[n][0] and nit[n][1]: nit[n][1] = False
        for c in range(NC):
            if not req[c] and nreq[c]: rises[c] += 1
        if not req[2] and nreq[2]: started = True
        closed = ack[out0] and not nack[out0]
        ch = (nreq != req) or (nack != ack) or (nit != it)
        req, ack, it = nreq, nack, nit
        for n, o in enumerate(ops):
            if o["k"] == "link": latch[o["o"]] = D[o["o"]]
        D2 = dats()
        for n, o in enumerate(ops):
            if o["k"] == "link": latch[o["o"]] = D2[o["o"]]
        D = D2
        changes += 1 if ch else 0
        if closed:
            return dict(ok=True, t=t + 1, val=D[out0], rises=rises, changes=changes)
    return dict(ok=False, why="tmax")


def main():
    nvec = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    nseed = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    names, ops, out0 = sim.load_net()
    sp = spine()
    vecs = [(12, 18), (1, 1), (0, 5), (7, 0), (35, 14), (100, 75), (17, 5), (64, 48)][:nvec]
    import math
    worst = dict(sp=0, ns=0, ch=0)
    bad = 0
    for (a, b) in vecs:
        for q in (1.0, 0.5, 0.25):
            for s in range(nseed if q < 1 else 1):
                r = run(a, b, names, ops, out0, q, random.Random(1000 * a + b + s))
                if not r["ok"]:
                    bad += 1; print(f"a={a} b={b} q={q} seed={s}: FAIL {r['why']}"); continue
                ms = max(r["rises"][c] for c in range(len(names)) if sp[c])
                mn = max(r["rises"][c] for c in range(len(names)) if not sp[c])
                cn = max(range(len(names)), key=lambda c: (not sp[c]) * r["rises"][c])
                ok = r["val"] == math.gcd(a, b)
                print(f"a={a} b={b} q={q} seed={s}: out0 closes t={r['t']} val={r['val']} "
                      f"{'=gcd' if ok else '!=gcd'} spine max offers {ms}, non-spine max {mn} "
                      f"({names[cn]}), projected changes {r['changes']}")
                bad += 0 if ok else 1
                worst["sp"] = max(worst["sp"], ms); worst["ns"] = max(worst["ns"], mn)
                worst["ch"] = max(worst["ch"], r["changes"])
    print(f"worst: spine offers {worst['sp']}, non-spine offers {worst['ns']}, changes {worst['ch']}; failures {bad}")


if __name__ == "__main__":
    main()
