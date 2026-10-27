#!/usr/bin/env python3
"""csim.py -- concrete fixed-delay transport simulation of an xaudit netlist (cross-check only).

    python3 -I csim.py NET.json BANDS.json --stim STIM.json [--mode rand|mid|lo|hi] [--seed N]
                      [--watch NET ...] [--dump-ps T1,T2 --dump NET ...]

The same netlist and band file xaudit reads (routed2x.py output).  Every element
(LUT output and routed arc, as xaudit splits them) gets ONE fixed delay in ps,
drawn from its band (--mode rand: uniform integer in [lo, hi]; mid/lo/hi), and the
circuit is simulated with binary values and pure transport delay (every pulse
propagates; no inertial filtering), event driven.  Power-up: every net 0, then
every gate evaluated once at t = 0 (so the reset period settles the loops).
This is NOT the audit; it samples single behaviours inside the bands, to tell a
flagged X window that a concrete behaviour reproduces (a real race under the
bands, if the defect shows) from one none of the samples shows (likely
abstraction imprecision -- sampling can never prove that).
"""
import argparse
import heapq
import json
import random
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("net")
    ap.add_argument("bands")
    ap.add_argument("--stim", required=True)
    ap.add_argument("--mode", default="rand", choices=["rand", "mid", "lo", "hi"])
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--watch", nargs="*", default=[])
    ap.add_argument("--bus", nargs="*", default=[], help="bus prefixes to print at each change of --strobe")
    ap.add_argument("--strobe", default=None, help="print buses when this net rises")
    ap.add_argument("--stop-after", type=int, default=0, help="stop after this many strobe rises")
    a = ap.parse_args()
    rnd = random.Random(a.seed)
    m = next(iter(json.load(open(a.net))["modules"].values()))
    B = json.load(open(a.bands))
    stim = json.load(open(a.stim))

    def pick(b):
        lo, hi = b
        if a.mode == "lo":
            return max(1, lo)
        if a.mode == "hi":
            return hi
        if a.mode == "mid":
            return max(1, (lo + hi) // 2)
        return max(1, rnd.randint(lo, hi))

    names = {}
    for nm, v in m["netnames"].items():
        names[nm] = v["bits"][0]
    val = {}
    gates = []          # (init, [input sources], out net, gate delay)
    sinks = {}          # net -> [(gate idx, pin idx, arc delay)]
    for cn, c in m["cells"].items():
        k = int(c["type"][3:])
        init = int(c["parameters"]["INIT"], 2)
        ins = []
        for i in range(k):
            b = c["connections"]["I%d" % i][0]
            ins.append(b)
        o = c["connections"]["O"][0]
        gi = len(gates)
        gates.append([init, [0] * k, o, pick(B["cells"][cn])])
        for i, b in enumerate(ins):
            if isinstance(b, str):
                gates[gi][1][i] = int(b)
            else:
                sinks.setdefault(b, []).append((gi, i, pick(B["arcs"]["%s/I%d" % (cn, i)])))
                val.setdefault(b, 0)
        val.setdefault(o, 0)
    ports = m["ports"]

    def portbits(p, v):
        out = []
        if p in ports:
            out.append((ports[p]["bits"][0], int(v)))
        else:
            for nm, pv in ports.items():
                if nm.startswith(p + "["):
                    i = int(nm[len(p) + 1:-1])
                    out.append((pv["bits"][0], (int(v) >> i) & 1))
        if not out:
            sys.exit("unknown port %s" % p)
        return out

    q = []
    seq = [0]

    def push(t, kind, a1, a2):
        seq[0] += 1
        heapq.heappush(q, (t, seq[0], kind, a1, a2))

    for p, v in stim.get("init", {}).items():
        for b, x in portbits(p, v):
            val[b] = x
            for gi, pi, d in sinks.get(b, []):
                gates[gi][1][pi] = x
    for e in stim.get("events", []):
        for p, v in e["set"].items():
            for b, x in portbits(p, v):
                push(e["t_ps"], "net", b, x)
    for gi in range(len(gates)):
        push(0, "eval", gi, None)
    H = stim.get("horizon_ps", 20000)
    watch = {names[w]: w for w in a.watch}
    strobe = names.get(a.strobe) if a.strobe else None
    busbits = {}
    for p in a.bus:
        for nm, b in names.items():
            if nm.startswith(p + "["):
                busbits.setdefault(p, {})[int(nm[len(p) + 1:-1])] = b
    nrise = 0
    nev = 0
    while q:
        t, _, kind, x, y = heapq.heappop(q)
        if t > H:
            break
        nev += 1
        if kind == "net":
            if val.get(x) == y:
                continue
            val[x] = y
            if x in watch:
                print("%9d ps  %s = %d" % (t, watch[x], y))
            if x == strobe and y == 1:
                nrise += 1
                s = "  ".join("%s=0x%x" % (p, sum(val[b] << i for i, b in bb.items()))
                              for p, bb in busbits.items())
                print("%9d ps  STROBE %s rise #%d  %s" % (t, a.strobe, nrise, s))
                if a.stop_after and nrise >= a.stop_after:
                    break
            for gi, pi, d in sinks.get(x, []):
                push(t + d, "pin", gi, (pi, y))
        elif kind == "pin":
            pi, v = y
            g = gates[x]
            if g[1][pi] == v:
                continue
            g[1][pi] = v
            push(t, "eval", x, None)
        else:
            g = gates[x]
            addr = sum(b << i for i, b in enumerate(g[1]))
            push(t + g[3], "net", g[2], (g[0] >> addr) & 1)
    print("events %d, end t %d ps" % (nev, t))


if __name__ == "__main__":
    main()
