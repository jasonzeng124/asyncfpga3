#!/usr/bin/env python3
"""Pipelined environment on C-wit's unit-delay simulation of the gcd_hw handshake network
(Formal/Net/CapstoneNet.lean ops; simulate() copied from formal/tools/capwit3/sim.py and
changed only in the environment).

THE goal (PROGRAM.md, owner 2026-10-31): the environment may offer pair k+1 as soon as the
input handshake of pair k completes, without waiting for its output.  Mode "pipe": every
source request is one wire env_c (a bd_fork over a, b, start, as in gcd_rig.v), in_ack =
C(source acks), and env_c' = not in_ack: a free-running four-phase source that raises the
request for pair k+1 as soon as in_ack has fallen for pair k.  out0 is acknowledged by a
delay-1 sink.  Every gate has delay 1 (ONE delay assignment, not a band).

usage: hwsim.py a1,b1 a2,b2 ...   prints the out0 values in the order they are offered.
Untrusted exploration tool; a finding is re-checked in Lean.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "capwit3"))
from sim import load_net, Cel, ev, jval, sel2, selD, NINT, ins_of, outs_of  # noqa: E402

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
    rig = env["mode"] in ("rig", "pipe")
    pipe = env["mode"] == "pipe"
    offer = [0]
    noack = env.get("noack", False)   # negative control: uenv1 replaced by an inverter of in_ack
    srcz = [o["z"] for o in ops if o["k"] == "src"]
    if rig:
        envc, inack, rises = True, False, 0
        for z in srcz: req[z] = True
    it = {n: [False] * NINT.get(o["k"], 0) for n, o in enumerate(ops)}
    latch = {o["o"]: 0 for o in ops if o["k"] == "link"}
    srcdone = {n: False for n, o in enumerate(ops) if o["k"] == "src"}
    srcleft = {n: (env.get("start_tokens", 1) if o["z"] == env.get("start") else 1)
               for n, o in enumerate(ops) if o["k"] == "src"}
    srcv = lambda w: vals[min(offer[0], len(vals) - 1)][w]

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
                if rig and not pipe and o["i"] == env["out0"]:
                    # uenv0 = C(res_req, not env_c), res_req abstracted to out0.req
                    nack[o["i"]] = Cel(ack[o["i"]], [req[o["i"]], not envc])
                else:
                    nack[o["i"]] = req[o["i"]]
        if rig:
            nin = Cel(inack, [ack[z] for z in srcz])
            ne = (not inack) if (noack or pipe) else Cel(envc, [ack[env["out0"]], not inack])
            if ne and not envc:
                if rises + 1 < env["offers"]:
                    rises += 1
                    offer[0] = rises
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




def main():
    pairs = [tuple(int(x, 0) for x in p.split(",")) + (0,) for p in sys.argv[1:]] or [(12, 18, 0)]
    names, ops, out0, start = load_net("gcd")
    env = {"mode": "pipe", "offers": len(pairs), "start": start, "out0": out0}
    tr = simulate(pairs, names, ops, env)
    T = len(tr)
    offs = [t for t in range(T - 1) if not tr[t][0][out0] and tr[t + 1][0][out0]]
    srises = [t for t in range(T - 1) if not tr[t][0][start] and tr[t + 1][0][start]]
    print(f"pairs {[p[:2] for p in pairs]}: quiescent after {T - 1} ticks")
    print(f"start.req rises at {[0] + srises if tr[0][0][start] else srises}")
    print(f"out0 offered at {offs}, values {[tr[t + 1][3][out0] for t in offs]}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
