#!/usr/bin/env python3
"""C-witgen: unit-delay simulation of a CapNet network at the GENERATED-NETLIST level.

Where C-8t / C-wit (capwit, capwit2: `sim.py`) simulate the lumped Ops gate models (`Cell`),
this file simulates the per-LUT structure that O4's `GenCell` (Formal/Net/CellBindOps.lean)
and O4b's `GenCellKP` (CellBindPersistK.lean) quantify over, with bdc's own chain shapes:

* fork N <= 4: one C-element LUT on the branch acks; N = 5: chunk C4 node `m` + top C2;
  N = 6: C4 node `m1`, C2 node `m2`, top C2 (bd_ctree as generated). `req_out[k]` is a route
  of one tick (H_WIRE_DI).
* compute unit (`join`): bd_join C-element `m` (N = 2) or the input request (N = 1), then
  `uor` (LUT1) and `bd_delay_gated #(.N(DJ))`: stages buf(x0), buf(x1), then
  x_k = x_{k-1} AND x0 (the gate is the joined request itself) -- DJ + 1 stages in all.
  `ack_out[k]` routes of one tick.
* bjoin: the C-element LUT; ack routes of one tick.
* steer: the LUT6_2 and `uack` OR, one tick each (as C-8t).
* mux: uj0/uj1/uxa/uya C-elements, `uor` OR node `e`, plain `bd_delay #(.N(DM))` (DM buffer
  stages) to z_req; ctl_ack route of one tick.
* muxN: three join C-elements, three ack C-elements, the `|j` node `e` (OR), then `uor` +
  `bd_delay_gated #(.N(DN))` gated by `e` (DN + 1 stages).
* amerge: grants g1/g2 (as C-8t), `R0` = g1 OR g2 at the same tick (H_R0_ISO: `ustate.O5`
  and the grants are LUTs of the same state node), then `uor` + `bd_delay_gated #(.N(DA))`.
* link: controller LUT `c`, `rdly` = plain bd_delay of DL stages + one route stage
  (DL + 1 buffer nodes), `uack` = bd_delay FASTRISE of DK stages (buf(c), then
  x_k = x_{k-1} OR c) + one route stage (DK + 1 nodes).
* src: LUT1 inverter; sink: the ack route (one tick).

Every node has delay exactly 1 (its value at t+1 is its function of the values at t), except
R0 (same tick, see above). Environment as C-8t: each source offers one token then waits.
The Python checks below mirror the Lean checker (untrusted; the kernel re-checks).
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sim  # noqa: E402  (capwit3's copy of capwit2/sim.py)

# chain lengths (bdc parameters): defaults are the smallest DELAY bdc's tightened gcd_kernel.v
# uses for compute units (12) and muxes (12), the amerge default (4), the link's most common
# non-zero DELAY (3) and DACK (6).
LEN = dict(DJ=12, DM=12, DN=12, DA=4, DL=3, DK=6)


def gated(N):
    """bd_delay_gated #(.N(N)) behind `uor`, from x0: [('buf',0), ('buf',1), ('and',k-1,0)...]."""
    return [("buf", 0), ("buf", 1)] + [("and", k - 1, 0) for k in range(3, N + 2)]


def uackst(D):
    """bd_delay #(.N(D), .FASTRISE(1)) from c, then one route stage."""
    return [("buf", 0)] + [("or", k - 1, 0) for k in range(2, D + 1)] + [("buf", D)]


def sG(st, x):
    if st[0] == "buf": return x(st[1])
    if st[0] == "and": return x(st[1]) and x(st[2])
    return x(st[1]) or x(st[2])


def cel(cur, vals):
    return vals[0] if all(v == vals[0] for v in vals) else cur


def plan(ops, L):
    """Per operator: (#m nodes, chain-A stages or None, buffer chain length or 0)."""
    P = []
    for o in ops:
        k = o["k"]
        if k in ("forkG", "forkH"):
            N = len(o["os"]); P.append((1 if N == 5 else 2 if N == 6 else 0, None, 0))
        elif k == "join":
            P.append((1 if len(o["ins"]) >= 2 else 0, gated(L["DJ"]), 0))
        elif k == "mux": P.append((1, None, L["DM"]))
        elif k == "muxn": P.append((1, gated(L["DN"]), 0))
        elif k == "amerge": P.append((1, gated(L["DA"]), 0))
        elif k == "link": P.append((0, uackst(L["DK"]), L["DL"] + 1))
        else: P.append((0, None, 0))
    return P


def simulate(vals, names, ops, L=LEN, tmax=200000):
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
            elif k == "src": v = vals[o["which"]]
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
                z = o["z"]
                if req[z]: nreq[z] = not ack[z]
                elif not srcdone[n]: nreq[z] = not ack[z]
            elif k == "sink":
                nack[o["i"]] = req[o["i"]]
            # chain A
            if P[n][1]:
                st = P[n][1]; N = len(st)
                xa = lambda j, n=n, N=N: x0A(n) if j == 0 else (ca[n][j - 1] if j < N else
                                                               (req if endA(n)[0] == "req" else ack)[endA(n)[1]])
                for kk in range(1, N + 1):
                    v = sG(st[kk - 1], xa)
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
        for n, o in enumerate(ops):
            if o["k"] == "src" and not req[o["z"]] and nreq[o["z"]]:
                srcdone[n] = True
        changed = (nreq != req) or (nack != ack) or (nit != it) or (nmm != mm) or (nca != ca) or (ncb != cb)
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


def gen_check(ops, tr, P):
    """Python mirror of the generated-level conditions (`GenCell` beyond the lumped `Cell`)."""
    T = len(tr)
    S = lambda t: tr[min(t, T - 1)]
    R = lambda c, t: S(t)[0][c]
    A = lambda c, t: S(t)[1][c]
    I = lambda n, k, t: S(t)[2][n][k]
    Mm = lambda n, k, t: S(t)[4][n][k]
    errs = []

    def need(c, m):
        if not c: errs.append(m)

    def mv(f, t): return f(t + 1) != f(t)

    for n, o in enumerate(ops):
        k = o["k"]
        x0 = None
        for t in range(T + 1):
            if k in ("forkG", "forkH"):
                a = [(lambda t, c=c: A(c, t)) for c in o["os"]]; r = lambda t: A(o["i"], t); N = len(a)
                if N <= 4:
                    if mv(r, t): need(r(t + 1) == cel(r(t), [f(t) for f in a]), (n, "tree", t))
                else:
                    m1 = lambda t: Mm(n, 0, t)
                    if mv(m1, t): need(m1(t + 1) == cel(m1(t), [f(t) for f in a[:4]]), (n, "m1", t))
                    if N == 5:
                        if mv(r, t): need(r(t + 1) == cel(r(t), [m1(t), a[4](t)]), (n, "top5", t))
                    else:
                        m2 = lambda t: Mm(n, 1, t)
                        if mv(m2, t): need(m2(t + 1) == cel(m2(t), [f(t) for f in a[4:]]), (n, "m2", t))
                        if mv(r, t): need(r(t + 1) == cel(r(t), [m1(t), m2(t)]), (n, "top6", t))
                    for f in a:
                        if mv(f, t): need(f(t) == r(t), (n, "leafpersist", t))
            if k == "join":
                for i in o["ins"]:
                    if mv(lambda t: R(i, t), t): need(R(i, t) == R(o["o"], t), (n, "join leafpersist", t))
                if len(o["ins"]) == 2:
                    m = lambda t: Mm(n, 0, t)
                    if mv(m, t): need(m(t + 1) == cel(m(t), [R(i, t) for i in o["ins"]]), (n, "join m", t))
            if k == "mux":
                e = lambda t: Mm(n, 0, t)
                if mv(e, t): need(e(t + 1) == (I(n, 0, t) or I(n, 1, t)), (n, "uor", t))
                for kk in (0, 1):
                    if mv(lambda t: I(n, kk, t), t): need(I(n, kk, t) == R(o["z"], t), (n, "mux leafpersist", t))
            if k == "muxn":
                e = lambda t: Mm(n, 0, t)
                if mv(e, t): need(e(t + 1) == (I(n, 0, t) or I(n, 1, t) or I(n, 2, t)), (n, "|j", t))
                for kk in (0, 1, 2):
                    if mv(lambda t: I(n, kk, t), t): need(I(n, kk, t) == R(o["z"], t), (n, "muxn leafpersist", t))
        # chains
        if P[n][1]:
            st = P[n][1]; N = len(st)
            if k == "join": x0 = (lambda t: Mm(n, 0, t)) if P[n][0] else (lambda t: R(o["ins"][0], t))
            elif k == "muxn": x0 = lambda t: Mm(n, 0, t)
            elif k == "amerge": x0 = lambda t: Mm(n, 0, t)
            else: x0 = lambda t: I(n, 0, t)
            end = (lambda t: R(o["o"], t)) if k == "join" else (lambda t: R(o["z"], t)) if k in ("muxn", "amerge") \
                else (lambda t: A(o["i"], t))
            x = lambda j, t: x0(t) if j == 0 else (S(t)[5][n][j - 1] if j < N else end(t))
            for t in range(T + 1):
                for kk in range(1, N + 1):
                    if x(kk, t + 1) != x(kk, t):
                        need(x(kk, t + 1) == sG(st[kk - 1], lambda j: x(j, t)), (n, "chainA si", kk, t))
                if x0(t + 1) != x0(t):
                    need(all(x(j, t) == x0(t) for j in range(N + 1)), (n, "SETTLED", t))
                if k == "amerge" and end(t + 1) != end(t):
                    need(x0(t) == (I(n, 0, t) or I(n, 1, t)), (n, "R0_ISO", t))
        if P[n][2]:
            N = P[n][2]
            x0 = (lambda t: Mm(n, 0, t)) if k == "mux" else (lambda t: I(n, 0, t))
            end = (lambda t: R(o["z"], t)) if k == "mux" else (lambda t: R(o["o"], t))
            x = lambda j, t: x0(t) if j == 0 else (S(t)[6][n][j - 1] if j < N else end(t))
            for t in range(T + 1):
                for kk in range(1, N + 1):
                    if x(kk, t + 1) != x(kk, t): need(x(kk, t + 1) == x(kk - 1, t), (n, "chainB si", kk, t))
                if x0(t + 1) != x0(t): need(end(t) == x0(t), (n, "PERSISTEND", t))
    return errs


def run(net, vals, L=LEN):
    names, ops, out0, start = sim.load_net(net)
    tr, P = simulate(vals, names, ops, L)
    env = {"mode": "once", "start": start, "out0": out0}
    # the lumped Cell check of capwit2 reads (req, ack, it, dat) = the first four components
    errs, falls = sim.check(vals, names, ops, out0, start, [s[:4] for s in tr], env)
    errs = errs + gen_check(ops, tr, P)
    return names, ops, out0, start, tr, P, errs, falls


def main():
    args = [x for x in sys.argv[1:] if not x.startswith("--")]
    net = args[0] if args else "gcd"
    vals = [int(x) for x in args[1:]] or [12, 18]
    vals = vals + [0]
    names, ops, out0, start, tr, P, errs, falls = run(net, vals)
    T = len(tr)
    tg = lambda xs: len(sim.toggles(xs))
    nt = sum(tg([s[0][c] for s in tr]) + tg([s[1][c] for s in tr]) for c in range(len(names)))
    ni = 0
    for n in range(len(ops)):
        for comp in (2, 4, 5, 6):
            for kk in range(len(tr[0][comp][n])):
                ni += tg([s[comp][n][kk] for s in tr])
    print(f"{net} {vals}: quiescent after {T - 1} ticks, {nt} channel req/ack toggles, {ni} internal-node toggles")
    print(f"out0 closes at {falls}, values {[tr[e][3][out0] for e in falls]}")
    print(f"{len(errs)} violations", errs[:20])
    return 0 if not errs else 1


if __name__ == "__main__":
    sys.exit(main())
