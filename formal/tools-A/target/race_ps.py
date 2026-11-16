#!/usr/bin/env python3
"""race_ps.py (shard A, 2026-11-16; UNTRUSTED analysis): one race in picoseconds, as the owner asks (PROGRAM.md,
"A kappa is not a result").

    python3 race_ps.py NET.json DUMP.json Q PIN CORNER [--mode M|F|S] [--top 3]

DUMP is a simx --dump of a run with NO slow class (--classes {"S":[],"F":[]}) at --kappa 0, --cdefault MODE, CORNER,
--w 0: then every arc's delay is known exactly (simx: M = (FN+FX)//2, F = FN, S = FX with FN/FX the arc's fast or
slow window ends), so every output flip can be explained by one input arrival (flip + that pin's delay).

Q is a storage gate's output node (e.g. SLICE_X10Y26.A6) and PIN the pin the margin tool slowed (the enable in the
latch-enable races). For every arrival at PIN, the first LATER arrival at another pin of Q that Q depends on (its own
feedback excluded) is found; the smallest gaps are reported. For each, both arrivals are traced back, flip by flip,
to the latest event they share (the split, the "common launch"); each path from the split is printed with its delay
split into cells (LUT, MUXF, CARRY arcs: site pin + IOPATH, prjxray) and routing (pips and site hops).
The gap is the slack of THAT race at that delay assignment: how much later the PIN path could be (or how much earlier
the other path) before the order flips. Not a proof, and only the arrivals the run's vectors make.
"""
import argparse, json, sys
from bisect import bisect_right

ap = argparse.ArgumentParser()
ap.add_argument("net"); ap.add_argument("dump"); ap.add_argument("q"); ap.add_argument("pin", type=int)
ap.add_argument("corner", type=int); ap.add_argument("--mode", default="M"); ap.add_argument("--top", type=int, default=3)
ap.add_argument("--other", type=int, nargs="*", default=None, help="restrict the other arrival to these pins (the data pins)")
a = ap.parse_args()
net = json.load(open(a.net)); N = net["nodes"]; G = net["gates"]; idx = {n: i for i, n in enumerate(N)}
drv = {g["out"]: gi for gi, g in enumerate(G)}
D = json.load(open(a.dump)); H = {int(k): v[1] for k, v in D["nodes"].items()}; R0 = D["args"]["R"]


def dl(e):
    FN, FX = (e["smin"], e["smax"]) if a.corner else (e["fmin"], e["fmax"])
    return {"M": (FN + FX) // 2, "F": FN, "S": FX}[a.mode]


def dep(g, j):
    k, I = g["k"], g["init"]
    return any(((I >> x) & 1) != ((I >> (x ^ (1 << j))) & 1) for x in range(1 << k))


def cause(node, t):
    """the (input node, flip time, pin, gate) whose arrival made `node` flip at t, or None (env / no driver)."""
    if node not in drv:
        return None
    gi = drv[node]; g = G[gi]
    best = None
    for p, u in enumerate(g["ins"]):
        tf = t - dl(g["arcs"][p])
        fl = H.get(u, [])
        i = bisect_right(fl, tf) - 1
        if i >= 0 and fl[i] == tf and (best is None or dep(g, p)):
            best = (u, tf, p, gi)
    return best


def chain(node, t, lim=4000):
    out = [(node, t, None, None)]
    while len(out) < lim:
        c = cause(node, t)
        if c is None:
            break
        u, tf, p, gi = c
        out[-1] = (node, t, p, gi)
        out.append((u, tf, None, None)); node, t = u, tf
    return out


def cls(g): return "cell" if g["kind"] in ("lut6", "lut5", "muxf", "carry") else "route"


qn = idx[a.q]; gq = G[drv[qn]]
def src_of(u):
    while u in drv and G[drv[u]]["k"] == 1 and G[drv[u]]["init"] == 2:
        u = G[drv[u]]["ins"][0]
    return u


fb = [j for j, u in enumerate(gq["ins"]) if src_of(u) == qn]   # own feedback, through its copy chain
pin_src = gq["ins"][a.pin]
arr_pin = [t + dl(gq["arcs"][a.pin]) for t in H.get(pin_src, []) if t >= R0]
oth = sorted((t + dl(gq["arcs"][j]), j) for j in range(gq["k"]) if j != a.pin and j not in fb and dep(gq, j) and (a.other is None or j in a.other)
             for t in H.get(gq["ins"][j], []) if t >= R0)
gaps = []
for tp in arr_pin:
    i = bisect_right(oth, (tp, 99))
    if i < len(oth):
        gaps.append((oth[i][0] - tp, tp, oth[i][0], oth[i][1]))
gaps.sort()
print("race at %s (gate %s): pin %d (source %s) from %s vs the next arrival on another pin; corner %d, mode %s, w 0; %d arrivals "
      "at pin %d" % (a.q, gq["name"], a.pin, N[src_of(pin_src)], N[pin_src], a.corner, a.mode, len(arr_pin), a.pin))
for gap, tp, to, j in gaps[:a.top]:
    ca = chain(gq["ins"][a.pin], tp - dl(gq["arcs"][a.pin]))
    cb = chain(gq["ins"][j], to - dl(gq["arcs"][j]))
    sa = {(n, t): k for k, (n, t, _, _) in enumerate(ca)}
    split = None
    for k, (n, t, _, _) in enumerate(cb):
        if (n, t) in sa:
            split = (sa[(n, t)], k); break
    print("\n  gap %d ps: pin %d arrival %d, pin %d arrival %d" % (gap, a.pin, tp, j, to))
    if split is None:
        print("  no common event found within %d / %d flips back (one path starts at the environment)" % (len(ca), len(cb)))
        continue
    ka, kb = split
    print("  split: %s flips at %d ps" % (N[ca[ka][0]], ca[ka][1]))
    for lab, ch, k, p, tarr in (("pin %d (the slowed pin)" % a.pin, ca, ka, a.pin, tp), ("pin %d (other)" % j, cb, kb, j, to)):
        cell = route = 0; luts = []
        for n, t, pp, gi in ch[:k]:
            g = G[gi]; d = dl(g["arcs"][pp])
            if cls(g) == "cell":
                cell += d; luts.append(g["name"])
            else:
                route += d
        dq = dl(gq["arcs"][p]); cell += dq   # the last arc, into Q's pin (site pin + IOPATH: a cell arc)
        print("  path to %-26s %6d ps = cells %6d + routing %6d; %d gates, %d LUT/MUX/CARRY: %s"
              % (lab, tarr - ch[k][1], cell, route, k, len(luts), " <- ".join(luts[:12]) + (" ..." if len(luts) > 12 else "")))
