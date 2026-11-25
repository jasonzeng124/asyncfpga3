#!/usr/bin/env python3
"""Pipelined environment on C-witgen's GENERATED-NETLIST-level unit-delay simulation of gcd_hw
(simulate() copied from formal/tools/capwit3/simgen.py; only the environment changed): the
sources are one request env_c (bd_fork over a, b, start), in_ack = C(source acks), and
env_c' = not in_ack, so pair k+1 is offered as soon as pair k's input handshake completes.
`--delay SEED SPREAD`: every node gets a fixed random inertial delay in [1, SPREAD] ticks
(exploration of other delay assignments; untrusted).

usage: hwsimgen.py [--delay SEED SPREAD] a1,b1 a2,b2 ...
"""
import os, sys, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "capwit3"))
import sim  # noqa: E402
from simgen import LEN, gated, uackst, sG, cel, plan  # noqa: E402

def simulate(vals, names, ops, L=LEN, tmax=400000, mut=None, delay=None):
    """`mut` (negative controls only): {'slowhead': (op, D)} gives chain A's first node of operator
    `op` an inertial delay of D ticks; {'init5': (op, pat)} flips one INIT bit of fork `op`'s N = 5 chunk
    C-element (leaves a0..a3 = pat with q = 0 sets m)."""
    mut = mut or {}
    pend = {}
    NC = len(names)
    prod = {}
    for n, o in enumerate(ops):
        for c in sim.outs_of(o): prod[c] = n
    P = plan(ops, L)
    req = [False] * NC; ack = [False] * NC
    it = {n: [False] * sim.NINT.get(o["k"], 0) for n, o in enumerate(ops)}
    mm = {n: [False] * P[n][0] for n in range(len(ops))}
    ca = {n: [False] * (len(P[n][1]) - 1 if P[n][1] else 0) for n in range(len(ops))}
    cb = {n: [False] * (P[n][2] - 1 if P[n][2] else 0) for n in range(len(ops))}
    latch = {o["o"]: 0 for o in ops if o["k"] == "link"}
    srcdone = {n: False for n, o in enumerate(ops) if o["k"] == "src"}
    srcz = [o["z"] for o in ops if o["k"] == "src"]
    env = {"c": False, "in": False, "offer": 0, "rises": 0}

    def dats():
        memo = {}

        def d(c):
            if c in memo: return memo[c]
            o = ops[prod[c]]; k = o["k"]
            if k in ("forkG", "forkH"): v = d(o["i"])
            elif k == "join": v = sim.ev(o["e"], [sim.jval(j, [d(i) for i in o["ins"]]) for j in o["js"]])
            elif k == "bjoin":
                vs = [d(i) for i in o["ins"]]
                v = 2 * sim.ev(o["ed"], vs) + sim.ev(o["ec"], vs) % 2
            elif k == "steerC": v = 0
            elif k == "steerD": v = sim.ev(o["fd"], [d(o["j"]) // 2])
            elif k == "mux": v = d(o["y"]) if sim.sel2(d(o["c"])) else d(o["x"])
            elif k == "muxn": v = d(o["xs"][sim.selD(d(o["c"]))])
            elif k == "amerge":
                g = it[prod[c]]
                won = g[1] or ack[o["y"]]
                v = 2 * (d(o["y"]) if won else d(o["x"])) + (1 if won else 0)
            elif k == "link": v = d(o["i"]) if it[prod[c]][0] else latch[c]
            elif k == "src": v = vals[env["offer"]][o["which"]]
            else: raise ValueError(k)
            memo[c] = v
            return v
        return [d(c) for c in range(NC)]

    def r0(n): return it[n][0] or it[n][1]

    def x0A(n):   # chain-A input
        o = ops[n]; k = o["k"]
        if k == "join": return mm[n][0] if mm[n] else req[o["ins"][0]]
        if k in ("muxn",): return mm[n][0]
        if k == "amerge": return r0(n)
        if k == "link": return it[n][0]
        raise ValueError(k)

    def endA(n):  # (is_req, channel) of chain A's last node
        o = ops[n]; k = o["k"]
        if k in ("join", "muxn", "amerge"): return ("req", o["o"] if k == "join" else o["z"])
        return ("ack", o["i"])

    def x0B(n):
        o = ops[n]
        return mm[n][0] if o["k"] == "mux" else it[n][0]

    def endB(n):
        o = ops[n]
        return o["z"] if o["k"] == "mux" else o["o"]

    trace = []
    D = dats()

    def snap():
        for n, o in enumerate(ops):
            if o["k"] == "amerge": mm[n][0] = r0(n)   # R0 = g1 OR g2, same tick (H_R0_ISO)
        return (list(req), list(ack), {n: list(v) for n, v in it.items()},
                D, {n: list(v) for n, v in mm.items()}, {n: list(v) for n, v in ca.items()},
                {n: list(v) for n, v in cb.items()}, {n: r0(n) for n, o in enumerate(ops) if o["k"] == "amerge"})
    trace.append(snap())
    for t in range(tmax):
        nreq, nack = list(req), list(ack)
        nit = {n: list(v) for n, v in it.items()}
        nmm = {n: list(v) for n, v in mm.items()}
        nca = {n: list(v) for n, v in ca.items()}
        ncb = {n: list(v) for n, v in cb.items()}
        for n, o in enumerate(ops):
            k = o["k"]; g = it[n]
            if k in ("forkG", "forkH"):
                for c in o["os"]: nreq[c] = req[o["i"]]
                a = [ack[c] for c in o["os"]]; N = len(a); r = ack[o["i"]]
                if N <= 4: nack[o["i"]] = cel(r, a)
                elif N == 5:
                    nmm[n][0] = cel(mm[n][0], a[:4]); nack[o["i"]] = cel(r, [mm[n][0], a[4]])
                    if mut.get("init5", (None,))[0] == n and a[:4] == mut["init5"][1] and not mm[n][0]:
                        nmm[n][0] = True
                else:
                    nmm[n][0] = cel(mm[n][0], a[:4]); nmm[n][1] = cel(mm[n][1], a[4:])
                    nack[o["i"]] = cel(r, [mm[n][0], mm[n][1]])
            elif k == "bjoin":
                nreq[o["o"]] = cel(req[o["o"]], [req[i] for i in o["ins"]])
                for i in o["ins"]: nack[i] = ack[o["o"]]
            elif k == "join":
                if mm[n]: nmm[n][0] = cel(mm[n][0], [req[i] for i in o["ins"]])
                for i in o["ins"]: nack[i] = ack[o["o"]]
            elif k in ("steerC", "steerD"):
                j = o["j"]; s = sim.sel2(D[j])
                nreq[o["t"]] = req[j] and s
                nreq[o["f"]] = req[j] and not s
                nack[j] = ack[o["t"]] or ack[o["f"]]
            elif k == "mux":
                c, x, y, z = o["c"], o["x"], o["y"], o["z"]; s = sim.sel2(D[c])
                nit[n][0] = cel(g[0], [req[x], req[c] and not s])
                nit[n][1] = cel(g[1], [req[y], req[c] and s])
                nmm[n][0] = g[0] or g[1]
                nack[x] = cel(ack[x], [g[0], ack[z]])
                nack[y] = cel(ack[y], [g[1], ack[z]])
                nack[c] = ack[z]
            elif k == "muxn":
                c, z = o["c"], o["z"]; s = sim.selD(D[c])
                for m in range(3):
                    nit[n][m] = cel(g[m], [req[o["xs"][m]], req[c] and s == m])
                nmm[n][0] = g[0] or g[1] or g[2]
                for m in range(3):
                    x = o["xs"][m]
                    nack[x] = cel(ack[x], [g[m], ack[z]])
                nack[c] = ack[z]
            elif k == "amerge":
                x, y, z = o["x"], o["y"], o["z"]
                g1, g2 = g
                ng1 = req[x] if g1 else (req[x] and not g2 and not ack[z])
                ng2 = req[y] if g2 else (req[y] and not g1 and not ack[z] and not ng1)
                nit[n] = [ng1, ng2]
                nack[x] = cel(ack[x], [g1, ack[z]])
                nack[y] = cel(ack[y], [g2, ack[z]])
            elif k == "link":
                i, oo = o["i"], o["o"]; c = g[0]
                r, q = req[i], ack[oo]
                nit[n][0] = (r and not q) or (c and (r or not q))
            elif k == "src":
                pass   # pipelined env below
            elif k == "sink":
                nack[o["i"]] = req[o["i"]]
            # chain A
            if P[n][1]:
                st = P[n][1]; N = len(st)
                xa = lambda j, n=n, N=N: x0A(n) if j == 0 else (ca[n][j - 1] if j < N else
                                                               (req if endA(n)[0] == "req" else ack)[endA(n)[1]])
                for kk in range(1, N + 1):
                    v = sG(st[kk - 1], xa)
                    if kk == 1 and mut.get("slowhead", (None,))[0] == n:
                        cur = xa(1)
                        pend[n] = pend.get(n, 0) + 1 if v != cur else 0
                        if v != cur and pend[n] < mut["slowhead"][1]: v = cur
                        elif v != cur: pend[n] = 0
                    if kk < N: nca[n][kk - 1] = v
                    else:
                        if endA(n)[0] == "req": nreq[endA(n)[1]] = v
                        else: nack[endA(n)[1]] = v
            if P[n][2]:
                N = P[n][2]
                xb = lambda j, n=n, N=N: x0B(n) if j == 0 else (cb[n][j - 1] if j < N else req[endB(n)])
                for kk in range(1, N + 1):
                    v = xb(kk - 1)
                    if kk < N: ncb[n][kk - 1] = v
                    else: nreq[endB(n)] = v
        excited = False
        if delay is not None:
            # inertial delays (exploration only): a node takes its new value only once the
            # excitation has persisted delay(key) ticks; otherwise it keeps its old value.
            def filt(key, old, new):
                nonlocal excited
                if new == old:
                    pend.pop(key, None); return old
                c = pend.get(key, 0) + 1
                if c < delay(key):
                    pend[key] = c; excited = True; return old
                pend.pop(key, None); return new
            for c in range(NC):
                nreq[c] = filt(("r", c), req[c], nreq[c]); nack[c] = filt(("a", c), ack[c], nack[c])
            for n in range(len(ops)):
                for k in range(len(it[n])): nit[n][k] = filt(("it", n, k), it[n][k], nit[n][k])
                if ops[n]["k"] != "amerge":
                    for k in range(len(mm[n])): nmm[n][k] = filt(("m", n, k), mm[n][k], nmm[n][k])
                for k in range(len(ca[n])): nca[n][k] = filt(("ca", n, k), ca[n][k], nca[n][k])
                for k in range(len(cb[n])): ncb[n][k] = filt(("cb", n, k), cb[n][k], ncb[n][k])
        # pipelined env: bd_fork over the sources; in_ack = C(source acks) (one tick);
        # env_c' = not in_ack (free-running four-phase), at most len(vals) offers.
        nin = cel(env["in"], [ack[z] for z in srcz])
        nc = not env["in"]
        if nc and not env["c"]:
            if env["rises"] < len(vals):
                env["offer"] = env["rises"]; env["rises"] += 1
            else: nc = False
        envchg = (nin, nc) != (env["in"], env["c"])
        env["in"], env["c"] = nin, nc
        for z in srcz: nreq[z] = nc
        changed = envchg or excited or (nreq != req) or (nack != ack) or (nit != it) or (nmm != mm) or (nca != ca) or (ncb != cb)
        req, ack, it, mm, ca, cb = nreq, nack, nit, nmm, nca, ncb
        for n, o in enumerate(ops):
            if o["k"] == "link": latch[o["o"]] = D[o["o"]]
        D2 = dats()
        for n, o in enumerate(ops):
            if o["k"] == "link": latch[o["o"]] = D2[o["o"]]
        changed = changed or (D2 != D)
        D = D2
        trace.append(snap())
        if not changed:
            return trace, P
    raise RuntimeError("no quiescence")




def main():
    argv = sys.argv[1:]
    delay = None
    if "--delay" in argv:
        i = argv.index("--delay"); seed, spread = int(argv[i + 1]), int(argv[i + 2]); del argv[i:i + 3]
        rng = random.Random(seed); memo = {}
        def delay(key):
            if key not in memo: memo[key] = rng.randint(1, spread)
            return memo[key]
    pairs = [tuple(int(x, 0) for x in p.split(",")) + (0,) for p in argv] or [(12, 18, 0)]
    names, ops, out0, start = sim.load_net("gcd")
    tr, P = simulate(pairs, names, ops, delay=delay)
    T = len(tr)
    R = lambda t, c: tr[t][0][c]
    offs = [t for t in range(T - 1) if not R(t, out0) and R(t + 1, out0)]
    sr = [t for t in range(T - 1) if not R(t, start) and R(t + 1, start)]
    print(f"pairs {[p[:2] for p in pairs]}: quiescent after {T - 1} ticks; start.req rises {sr}; "
          f"out0 offered at {offs}, values {[tr[t + 1][3][out0] for t in offs]}")

if __name__ == "__main__":
    main()
