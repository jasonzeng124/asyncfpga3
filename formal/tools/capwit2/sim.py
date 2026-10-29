#!/usr/bin/env python3
"""C-wit (copied from capwit/sim.py, C-8t, and generalised: any CapNet network file, per-source
values, initial request levels, and an environment policy; see `simulate`).

Original C-8t text: unit-delay simulation of the concrete gcd_hw circuit network (Formal/Net/CapstoneNet.lean).

Every gate of every operator's gate model (`CapNet.Cell`, the 8f/8j/8l cell models) is given
delay exactly 1: its output at t+1 is its excitation function of the signals at t (a C-element
holds when its inputs disagree). Data buses are the models' combinational functions of the
same tick; a link's latch is transparent while its `c` is high. The arbiter (`AMerge`) grants
input x when both request in the same tick. The three sources (`Src`) offer one token each and
then wait forever (allowed: H_LUT_SI is an unbounded inertial delay). The sinks acknowledge
with delay 1.

The run is checked here against every field of every cell model, `Held` on every channel,
H_START_ONCE, and the out0 value (Python mirror of the Lean checks; the Lean kernel re-checks
everything, so this file is untrusted).
"""
import os, re, sys, math

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, HERE)
import leanparse as LP  # noqa: E402

NETF = os.path.join(ROOT, "formal", "lean", "Formal", "Net", "CapstoneNet.lean")

M = lambda w: 1 << w


def flip(w, a): return (a % M(w) + (M(w - 1) if w >= 1 else 0)) % M(w)


def cmpi(p, w, a, b):
    x, y = a % M(w), b % M(w); sx, sy = flip(w, a), flip(w, b)
    return 1 if {"eq": x == y, "ne": x != y, "ult": x < y, "ule": x <= y, "ugt": y < x, "uge": y <= x,
                 "slt": sx < sy, "sle": sx <= sy, "sgt": sy < sx, "sge": sy <= sx}[p] else 0


def shrsi(w, a, b):
    if a % M(w) < M(w - 1): return (a % M(w)) >> b
    return (M(w) - 1) - ((M(w) - 1 - a % M(w)) >> b)


def ev(e, env):
    t = e[0]
    if t == "var": return env[e[1]] if e[1] < len(env) else 0
    if t == "lit": return e[1]
    if t == "un":
        o, w, a = e[1], e[2], ev(e[3], env)
        if o in ("trunci", "extui"): return a % M(w)
        dw = o[1]
        return a % M(w) if a % M(w) < M(w - 1) else a % M(w) + M(dw) - M(w)
    if t == "bin":
        o, w, a, b = e[1], e[2], ev(e[3], env), ev(e[4], env)
        if isinstance(o, tuple): return cmpi(o[1], w, a, b)
        return {"addi": lambda: (a + b) % M(w), "subi": lambda: (a % M(w) + M(w) - b % M(w)) % M(w),
                "muli": lambda: (a * b) % M(w), "andi": lambda: (a & b) % M(w),
                "ori": lambda: (a | b) % M(w), "xori": lambda: (a ^ b) % M(w),
                "shli": lambda: (a << b) % M(w), "shrui": lambda: (a % M(w)) >> b,
                "shrsi": lambda: shrsi(w, a, b)}[o]()
    s = ev(e[1], env)
    return ev(e[2], env) if s % 2 == 1 else ev(e[3], env)


def jval(j, vs):
    g = lambda p: vs[p] if p < len(vs) else 0
    if j[0] == "direct": return g(j[1])
    if j[0] == "fold": return ev(j[5], [g(j[2])])
    return ev(j[3], [])


def sel2(v): return v % 2 == 1
def selD(v): return 2 if v % 2 == 1 else v // 2 % 2


NETS = {
    "gcd": os.path.join(ROOT, "formal", "lean", "Formal", "Net", "CapstoneNet.lean"),
    "xorshift": os.path.join(ROOT, "formal", "lean", "Formal", "Net", "XorshiftCapData.lean"),
    "collatz": os.path.join(ROOT, "formal", "lean", "Formal", "Net", "CollatzCapData.lean"),
}
START = {"gcd": 2}   # gcd's start lives in CapstoneCutSpine; the KCap data files define `start`


def load_net(net="gcd"):
    txt = open(NETS[net]).read()
    names = re.findall(r'"([^"]*)"', re.search(r"def chanNames : List String := \[(.*?)\]\n", txt).group(1))
    body = re.search(r"def ops : List \(K NC\) := \[\n(.*?)\n\]", txt, re.S).group(1)
    ops = [LP.to_K(LP.parse(s.strip().rstrip(","))) for s in body.split("\n") if s.strip()]
    out0 = int(re.search(r"def out0 : Fin NC := (\d+)", txt).group(1))
    m = re.search(r"def start : Fin NC := (\d+)", txt)
    start = int(m.group(1)) if m else START[net]
    return names, ops, out0, start


def ins_of(o):
    k = o["k"]
    return {"forkG": lambda: [o["i"]], "forkH": lambda: [o["i"]], "join": lambda: o["ins"],
            "bjoin": lambda: o["ins"], "steerC": lambda: [o["j"]], "steerD": lambda: [o["j"]],
            "mux": lambda: [o["c"], o["x"], o["y"]], "muxn": lambda: [o["c"]] + o["xs"],
            "amerge": lambda: [o["x"], o["y"]], "link": lambda: [o["i"]], "src": lambda: [],
            "sink": lambda: [o["i"]]}[k]()


def outs_of(o):
    k = o["k"]
    return {"forkG": lambda: o["os"], "forkH": lambda: o["os"], "join": lambda: [o["o"]],
            "bjoin": lambda: [o["o"]], "steerC": lambda: [o["t"], o["f"]], "steerD": lambda: [o["t"], o["f"]],
            "mux": lambda: [o["z"]], "muxn": lambda: [o["z"]], "amerge": lambda: [o["z"]],
            "link": lambda: [o["o"]], "src": lambda: [o["z"]], "sink": lambda: []}[k]()


NINT = {"link": 1, "mux": 2, "muxn": 3, "amerge": 2}


def Cel(cur, vals):
    return vals[0] if all(v == vals[0] for v in vals) else cur


def simulate(vals, names, ops, env, tmax=100000):
    """`vals[w]`: the value source `which = w` offers. `env`:
    * {"mode": "once"}: every source offers one token, then waits (C-8t's environment);
    * {"mode": "rig", "start": s, "out0": o, "offers": N}: gcd_rig.v's environment. All
      source requests are the one wire `env_c` (bd_fork, `{N{req}}`), high at reset release
      (`uenv1` is a bd_c2n_set); `in_ack` = C(acks of the sources) (bd_fork's C-element);
      `env_c` = C(out0.ack, not in_ack) (uenv1); out0's acknowledge `env_c0` =
      C(out0.req, not env_c) (uenv0, with `res_req`'s CMPD delay line abstracted to the
      request itself, as the Sink model does). Every gate has delay 1. `env_c` is allowed to
      rise only N-1 times after reset (N offers in all), then holds: the run is finite.
    """
    NC = len(names)
    prod = {}
    for n, o in enumerate(ops):
        for c in outs_of(o): prod[c] = n
    req = [False] * NC; ack = [False] * NC
    rig = env["mode"] == "rig"
    srcz = [o["z"] for o in ops if o["k"] == "src"]
    if rig:
        envc, inack, rises = True, False, 0
        for z in srcz: req[z] = True
    it = {n: [False] * NINT.get(o["k"], 0) for n, o in enumerate(ops)}
    latch = {o["o"]: 0 for o in ops if o["k"] == "link"}
    srcdone = {n: False for n, o in enumerate(ops) if o["k"] == "src"}
    srcleft = {n: 1 for n, o in enumerate(ops) if o["k"] == "src"}
    srcv = lambda w: vals[w]

    def dats():
        memo = {}
        stack = set()

        def d(c):
            if c in memo: return memo[c]
            assert c not in stack, ("combinational data cycle", names[c])
            stack.add(c)
            o = ops[prod[c]]; k = o["k"]
            if k in ("forkG", "forkH"): v = d(o["i"])
            elif k == "join": v = ev(o["e"], [jval(j, [d(i) for i in o["ins"]]) for j in o["js"]])
            elif k == "bjoin":
                vs = [d(i) for i in o["ins"]]
                v = 2 * ev(o["ed"], vs) + ev(o["ec"], vs) % 2
            elif k == "steerC": v = 0
            elif k == "steerD": v = ev(o["fd"], [d(o["j"]) // 2])
            elif k == "mux": v = d(o["y"]) if sel2(d(o["c"])) else d(o["x"])
            elif k == "muxn": v = d(o["xs"][selD(d(o["c"]))])
            elif k == "amerge":
                g = it[prod[c]]
                won = g[1] or ack[o["y"]]
                v = 2 * (d(o["y"]) if won else d(o["x"])) + (1 if won else 0)
            elif k == "link": v = d(o["i"]) if it[prod[c]][0] else latch[c]
            elif k == "src": v = srcv(o["which"])
            else: raise ValueError(k)
            stack.discard(c)
            memo[c] = v
            return v
        return [d(c) for c in range(NC)]

    trace = []  # per tick: (req, ack, it, dat)
    D = dats()
    trace.append((list(req), list(ack), {n: list(v) for n, v in it.items()}, D))
    for t in range(tmax):
        nreq, nack = list(req), list(ack)
        if rig: renv = (envc, inack)
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
                nreq[o["t"]] = req[j] and s
                nreq[o["f"]] = req[j] and not s
                nack[j] = ack[o["t"]] or ack[o["f"]]
            elif k == "mux":
                c, x, y, z = o["c"], o["x"], o["y"], o["z"]; s = sel2(D[c])
                nit[n][0] = Cel(g[0], [req[x], req[c] and not s])
                nit[n][1] = Cel(g[1], [req[y], req[c] and s])
                nreq[z] = g[0] or g[1]
                nack[x] = Cel(ack[x], [g[0], ack[z]])
                nack[y] = Cel(ack[y], [g[1], ack[z]])
                nack[c] = ack[z]
            elif k == "muxn":
                c, z = o["c"], o["z"]; s = selD(D[c])
                for m in range(3):
                    nit[n][m] = Cel(g[m], [req[o["xs"][m]], req[c] and s == m])
                nreq[z] = g[0] or g[1] or g[2]
                for m in range(3):
                    x = o["xs"][m]
                    nack[x] = Cel(ack[x], [g[m], ack[z]])
                nack[c] = ack[z]
            elif k == "amerge":
                x, y, z = o["x"], o["y"], o["z"]
                g1, g2 = g
                ng1 = req[x] if g1 else (req[x] and not g2 and not ack[z])
                ng2 = req[y] if g2 else (req[y] and not g1 and not ack[z] and not ng1)
                nit[n] = [ng1, ng2]
                nreq[z] = g1 or g2
                nack[x] = Cel(ack[x], [g1, ack[z]])
                nack[y] = Cel(ack[y], [g2, ack[z]])
            elif k == "link":
                i, oo = o["i"], o["o"]; c = g[0]
                r, q = req[i], ack[oo]
                nit[n][0] = (r and not q) or (c and (r or not q))
                nack[i] = c
                nreq[oo] = c
            elif k == "src":
                z = o["z"]
                if rig: pass   # set below: the source requests are the wire env_c
                elif req[z]: nreq[z] = not ack[z]
                elif not srcdone[n]: nreq[z] = not ack[z]
            elif k == "sink":
                if rig and o["i"] == env["out0"]:
                    # uenv0 = C(res_req, not env_c), res_req abstracted to out0.req
                    nack[o["i"]] = Cel(ack[o["i"]], [req[o["i"]], not envc])
                else:
                    nack[o["i"]] = req[o["i"]]
        if rig:
            nin = Cel(inack, [ack[z] for z in srcz])
            ne = Cel(envc, [ack[env["out0"]], not inack])
            if ne and not envc:
                if rises + 1 < env["offers"]: rises += 1
                else: ne = envc
            envc, inack = ne, nin
            for z in srcz: nreq[z] = envc
        for n, o in enumerate(ops):
            if o["k"] == "src" and not req[o["z"]] and nreq[o["z"]]:
                srcleft[n] -= 1
                srcdone[n] = srcleft[n] == 0
        changed = (nreq != req) or (nack != ack) or (nit != it) or (rig and (envc, inack) != renv)
        # latch update: new value of link outputs at t+1
        req, ack, it = nreq, nack, nit
        for n, o in enumerate(ops):
            if o["k"] == "link": latch[o["o"]] = D[o["o"]]   # value at t, held if c(t+1) low
        D2 = dats()
        for n, o in enumerate(ops):
            if o["k"] == "link": latch[o["o"]] = D2[o["o"]]
        changed = changed or (D2 != D)
        D = D2
        trace.append((list(req), list(ack), {n: list(v) for n, v in it.items()}, D))
        if not changed:
            return trace
    raise RuntimeError("no quiescence")


def toggles(xs):
    return [t for t in range(len(xs) - 1) if xs[t + 1] != xs[t]]


def dchanges(xs):
    return [(t, xs[t + 1]) for t in range(len(xs) - 1) if xs[t + 1] != xs[t]]


def check(vals, names, ops, out0, start, tr, env):
    """Python mirror of every Lean condition, at every t of the trace (constant after)."""
    T = len(tr)
    NC = len(names)
    R = lambda c, t: tr[min(t, T - 1)][0][c]
    A = lambda c, t: tr[min(t, T - 1)][1][c]
    I = lambda n, k, t: tr[min(t, T - 1)][2][n][k]
    Dv = lambda c, t: tr[min(t, T - 1)][3][c]
    errs = []
    def need(cond, msg):
        if not cond: errs.append(msg)
    srcv = lambda w: vals[w]
    for n, o in enumerate(ops):
        k = o["k"]
        if k != "src":
            for c in outs_of(o): need(not R(c, 0), (n, "init req", c))
        for c in ins_of(o): need(not A(c, 0), (n, "init ack", c))
        for x in tr[0][2][n]: need(not x, (n, "init internal"))
        for t in range(T + 1):
            if k in ("forkG", "forkH"):
                for c in o["os"]:
                    if R(c, t + 1) != R(c, t): need(R(c, t + 1) == R(o["i"], t), (n, "fork wire", t))
                    need(Dv(c, t) == Dv(o["i"], t), (n, "fork dat", t))
                if A(o["i"], t + 1) != A(o["i"], t):
                    need(all(A(c, t) == A(o["i"], t + 1) for c in o["os"]), (n, "fork cel", t))
            elif k in ("join", "bjoin"):
                oo = o["o"]
                if R(oo, t + 1) != R(oo, t): need(all(R(i, t) == R(oo, t + 1) for i in o["ins"]), (n, "join cel", t))
                for i in o["ins"]:
                    if A(i, t + 1) != A(i, t): need(A(i, t + 1) == A(oo, t), (n, "join wire", t))
            elif k in ("steerC", "steerD"):
                j = o["j"]
                for bb, c in ((True, o["t"]), (False, o["f"])):
                    if R(c, t + 1) != R(c, t): need(R(c, t + 1) == (R(j, t) and sel2(Dv(j, t)) == bb), (n, "steer lut", t))
                if A(j, t + 1) != A(j, t): need(A(j, t + 1) == (A(o["t"], t) or A(o["f"], t)), (n, "steer orr", t))
            elif k == "mux":
                c, x, y, z = o["c"], o["x"], o["y"], o["z"]
                for m, inp, want in ((0, x, False), (1, y, True)):
                    if I(n, m, t + 1) != I(n, m, t):
                        need(R(inp, t) == I(n, m, t + 1) and (R(c, t) and sel2(Dv(c, t)) == want) == I(n, m, t + 1), (n, "mux cj", t))
                    if A(inp, t + 1) != A(inp, t):
                        need(I(n, m, t) == A(inp, t + 1) and A(z, t) == A(inp, t + 1), (n, "mux xa", t))
                if R(z, t + 1) != R(z, t): need(R(z, t + 1) == (I(n, 0, t) or I(n, 1, t)), (n, "mux zr", t))
                if A(c, t + 1) != A(c, t): need(A(c, t + 1) == A(z, t), (n, "mux ca", t))
            elif k == "muxn":
                c, z = o["c"], o["z"]
                for m in range(3):
                    inp = o["xs"][m]
                    if I(n, m, t + 1) != I(n, m, t):
                        need(R(inp, t) == I(n, m, t + 1) and (R(c, t) and selD(Dv(c, t)) == m) == I(n, m, t + 1), (n, "muxn cj", t))
                    if A(inp, t + 1) != A(inp, t):
                        need(I(n, m, t) == A(inp, t + 1) and A(z, t) == A(inp, t + 1), (n, "muxn xa", t))
                if R(z, t + 1) != R(z, t): need(R(z, t + 1) == (I(n, 0, t) or I(n, 1, t) or I(n, 2, t)), (n, "muxn zr", t))
                if A(c, t + 1) != A(c, t): need(A(c, t + 1) == A(z, t), (n, "muxn ca", t))
            elif k == "amerge":
                x, y, z = o["x"], o["y"], o["z"]
                g1 = lambda t: I(n, 0, t); g2 = lambda t: I(n, 1, t)
                if g1(t + 1) != g1(t): need(g1(t + 1) == R(x, t) and (not g1(t + 1) or (not g2(t) and not A(z, t))), (n, "arb1", t))
                if g2(t + 1) != g2(t): need(g2(t + 1) == R(y, t) and (not g2(t + 1) or (not g1(t) and not A(z, t))), (n, "arb2", t))
                need(not (g1(t) and g2(t)), (n, "excl", t))
                if R(z, t + 1) != R(z, t): need(R(z, t + 1) == (g1(t) or g2(t)), (n, "am zr", t))
                if not R(z, t) and R(z, t + 1): need(not A(x, t) and not A(y, t), (n, "RTZ", t))
                if A(x, t + 1) != A(x, t): need(g1(t) == A(x, t + 1) and A(z, t) == A(x, t + 1), (n, "am xa", t))
                if A(y, t + 1) != A(y, t): need(g2(t) == A(y, t + 1) and A(z, t) == A(y, t + 1), (n, "am ya", t))
            elif k == "link":
                i, oo = o["i"], o["o"]; c = lambda t: I(n, 0, t)
                if c(t + 1) != c(t):
                    r, q, cc = R(i, t), A(oo, t), c(t)
                    need(c(t + 1) == ((r and not q) or (cc and (r or not q))), (n, "link cel", t))
                if A(i, t + 1) != A(i, t): need(A(i, t + 1) == c(t), (n, "link ack", t))
                if R(oo, t + 1) != R(oo, t): need(R(oo, t + 1) == c(t), (n, "link req", t))
                if c(t): need(Dv(oo, t) == Dv(i, t), (n, "latch open", t))
                if not c(t + 1): need(Dv(oo, t + 1) == Dv(oo, t), (n, "latch hold", t))
            elif k == "src":
                z = o["z"]
                if R(z, t + 1) != R(z, t): need(R(z, t + 1) == (not A(z, t)), (n, "src", t))
                need(Dv(z, t) == srcv(o["which"]), (n, "src dat", t))
            elif k == "sink":
                i = o["i"]
                if A(i, t + 1) != A(i, t): need(A(i, t + 1) == R(i, t), (n, "sink", t))
    for c in range(NC):
        for t in range(T + 1):
            itx = lambda t: R(c, t) or A(c, t)
            if itx(t) and itx(t + 1): need(Dv(c, t + 1) == Dv(c, t), ("Held", names[c], t))
    rises = sum(1 for t in range(T) if not R(start, t) and R(start, t + 1))
    if env["mode"] == "once":
        need(rises == 1, ("start rises", rises))
    else:
        # RigEnv (CapstoneRigAll): s = start.req, k = out0.ack
        for t in range(T + 1):
            s0, s1, k0, k1 = R(start, t), R(start, t + 1), A(out0, t), A(out0, t + 1)
            if not s0 and s1: need(k0, ("RigEnv s_rise", t))
            if s0 and not s1: need(not k0, ("RigEnv s_fall", t))
            if not k0 and k1: need(not s0, ("RigEnv k_rise", t))
            if k0 and not k1: need(s0, ("RigEnv k_fall", t))
    falls = [t for t in range(T) if A(out0, t) and not A(out0, t + 1)]
    return errs, falls


def run(net, vals, env):
    names, ops, out0, start = load_net(net)
    if env["mode"] == "rig":
        env = dict(env, start=start, out0=out0)
    tr = simulate(vals, names, ops, env)
    errs, falls = check(vals, names, ops, out0, start, tr, env)
    return names, ops, out0, start, tr, errs, falls, env


def main():
    """sim.py NET V0 V1 ... [--rig N]"""
    argv = list(sys.argv[1:])
    env = {"mode": "once"}
    if "--rig" in argv:
        i = argv.index("--rig")
        env = {"mode": "rig", "offers": int(argv[i + 1])}
        del argv[i:i + 2]
    args = [x for x in argv if not x.startswith("--")]
    net = args[0] if args else "gcd"
    vals = [int(x) for x in args[1:]] or [12, 18]
    vals = vals + [0]   # the start source offers 0
    names, ops, out0, start, tr, errs, falls, env = run(net, vals, env)
    T = len(tr)
    nt = sum(len(toggles([s[0][c] for s in tr])) + len(toggles([s[1][c] for s in tr])) for c in range(len(names)))
    print(f"{net} {vals} {env['mode']}: quiescent after {T - 1} ticks, {nt} req/ack toggles")
    offs = [t for t in range(T - 1) if not tr[t][0][out0] and tr[t + 1][0][out0]]
    print(f"out0 offers at {offs}, values {[tr[t + 1][3][out0] for t in offs]}")
    print(f"out0 closes at {falls}, values {[tr[e][3][out0] for e in falls]}")
    srises = [t for t in range(T - 1) if not tr[t][0][start] and tr[t + 1][0][start]]
    print(f"start req0 {tr[0][0][start]}, rises at {srises}")
    print(f"{len(errs)} violations", errs[:20])
    quiet = [names[c] for c in range(len(names)) if not any(s[0][c] for s in tr)]
    print(f"{len(quiet)} channels never request:", quiet[:50])
    return 0 if not errs else 1


if __name__ == "__main__":
    sys.exit(main())
