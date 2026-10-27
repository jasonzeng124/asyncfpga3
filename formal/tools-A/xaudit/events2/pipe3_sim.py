#!/usr/bin/env python3
"""Random concrete transport simulation of the gate-level pipe3 control with its
environment (evidence only, for A-events2; NOT a proof).

Same model as `Events2.Beh` / `Events2Design.design_beh2` on `Events2Pipe3.D`:
Discrete time (1 step = 10 ps); every LUT, route, LUT1 delay buffer, own feedback,
reset arc and environment channel is a transport channel o(t) = i(f(t)), f(t) =
t - d(t) with d a random walk in [lo, hi], d(t+1) <= d(t) + 1 (so f is monotone and
the delay varies per event). Controllers are bd_c2n: reset -> 0, else maj(a, ~b, q).
Environment (default): eager sender req_in = NOT c0 delayed [1,50], eager receiver
ack_out = c2 delayed [1,50] (Events2Pipe3.envS / envR).

Checks against what Events2 PROVES, using the counter recursion computed from the
run's own warps (Beh.M, with the env pins' counts = toggle counts of the port):
  * safe: c_j(t) == ph(0, M(t, j)) at every t (pipe3_safe);
  * window: c0 toggles at most once in every 135 steps (pipe3_rates, cycle_le);
  * long run: event count of each stage within the proved rate bounds
    (135*M <= t + rho + 135, t <= 171*M + pi + T + 158).
Usage: pipe3_sim.py [runs] [--fb LO HI] [--openloop W]
  --openloop W: the SENDER ignores ack_in and toggles req_in every W steps (a
  square wave); the receiver stays eager. The rate bounds assume the eager sender
  and are not checked then.
"""
import random, sys

LUT, ROUTE, FB, ENV = (9, 13), (36, 44), (27, 33), (1, 50)

def walk(rnd, lo, hi, n):
    d = [rnd.randint(lo, hi)]
    for _ in range(n):
        nd = d[-1] + rnd.choice([-2, -1, 0, 0, 0, 1])
        d.append(min(hi, max(lo, nd, 0)) if nd <= d[-1] + 1 else d[-1] + 1)
    return d

def run(seed, fb=FB, openloop=None, T=200, H=8000):
    rnd = random.Random(seed)
    W = lambda b: walk(rnd, b[0], b[1], H + 10)
    # chains per pin: list of (band, inverting) from source to pin; env first
    src = {(0, 0): 0, (0, 1): 1, (1, 0): 0, (1, 1): 2, (2, 0): 1, (2, 1): 2}
    chains = {(0, 0): [(ENV, 1), (ROUTE, 0)], (0, 1): [(ROUTE, 0)],
              (1, 0): [(ROUTE, 0), (LUT, 0), (ROUTE, 0)], (1, 1): [(ROUTE, 0)],
              (2, 0): [(ROUTE, 0), (LUT, 0), (ROUTE, 0)], (2, 1): [(ENV, 0), (ROUTE, 0)]}
    neg = {0: 0, 1: 1}
    dch = {k: [W(b) for b, _ in ch] for k, ch in chains.items()}
    dF = [W(LUT) for _ in range(3)]
    dQ = [W(fb) for _ in range(3)]
    dR = [W(ROUTE) for _ in range(3)]
    c = [[0] for _ in range(3)]
    exc = [[0] for _ in range(3)]
    at = lambda sig, t: sig[max(t, 0)]
    def warp(d, t): return max(t - d[t], 0)
    # value of the port signal for open-loop runs
    def port(k, t):
        if t < T + 100: return 0
        return ((t - T - 100) // openloop) % 2 if k == (0, 0) else 0
    def G(k, s):           # composite warp of the pin channel: last link applied first
        for d in reversed(dch[k]):
            s = warp(d, s)
        return s
    def pinval(k, s):
        if openloop and k == (0, 0):
            return at_port(k, warp(dch[k][-1], s))
        inv = 0
        for _, i in chains[k]: inv ^= i
        return inv ^ at(c[src[k]], G(k, s))
    def at_port(k, s): return port(k, s)
    for t in range(1, H):
        for j in range(3):
            a = pinval((j, 0), t)
            b = pinval((j, 1), t)
            q = at(c[j], warp(dQ[j], t))
            r = 1 if warp(dR[j], t) < T else 0
            e = 0 if r else int((a and not b) or (a and q) or ((not b) and q))
            exc[j].append(e)
        for j in range(3):
            c[j].append(at(exc[j], warp(dF[j], t)))
    # the counter recursion over the same warps (Beh.M)
    off = {}
    for k, ch in chains.items():
        inv = 0
        for _, i in ch: inv ^= i
        off[k] = inv ^ neg[k[1]]
    tog = {}
    for k in (((0, 0),) if openloop else ()):     # open-loop env pin: count = toggles of the port up to s
        n, prev, arr = 0, port(k, 0), [0]
        for u in range(1, H + 1):
            v = port(k, u)
            if v != prev: n += 1
            prev = v; arr.append(n)
        tog[k] = arr
    togcount = lambda k, s: tog[k][s]
    M = [[0] * H for _ in range(3)]
    for t in range(1, H):
        for j in range(3):
            s = warp(dF[j], t)
            if warp(dR[j], s) < T:
                M[j][t] = 0; continue
            vals = []
            for p in (0, 1):
                k = (j, p)
                if openloop and k == (0, 0):
                    vals.append(togcount(k, warp(dch[k][-1], s)))
                else:
                    vals.append(M[src[k]][G(k, s)] + off[k])
            M[j][t] = min(vals)
    return c, M

def check(c, M, T=200):
    H = len(M[0])
    mism = sum(1 for j in range(3) for t in range(H) if c[j][t] != (M[j][t] % 2))
    ev = [[t for t in range(1, H) if c[j][t] != c[j][t - 1]] for j in range(3)]
    win = min((b - a for a, b in zip(ev[0], ev[0][1:])), default=None)
    rho, pi = [180, 90, 0], [0, 114, 228]
    rate_bad = sum(1 for j in range(3) for t in range(H)
                   if 135 * M[j][t] > t + rho[j] + 135 or t > 171 * M[j][t] + pi[j] + T + 158)
    sp = [(ev[j][-1] - ev[j][len(ev[j]) // 2]) / max(1, len(ev[j]) - 1 - len(ev[j]) // 2) for j in range(3) if len(ev[j]) > 4]
    return mism, win, rate_bad, [len(e) for e in ev], sp

if __name__ == "__main__":
    a = sys.argv[1:]
    runs = int(a[0]) if a and a[0].isdigit() else 50
    fb = (int(a[a.index("--fb") + 1]), int(a[a.index("--fb") + 2])) if "--fb" in a else FB
    ol = int(a[a.index("--openloop") + 1]) if "--openloop" in a else None
    bad = rb = 0; wmin = 10**9; smin, smax = 10**9, 0; nev = None
    for s in range(runs):
        c, M = run(s, fb=fb, openloop=ol)
        mism, win, rate_bad, n, sp = check(c, M)
        bad += mism > 0; rb += (rate_bad > 0) and not ol
        if win is not None: wmin = min(wmin, win)
        if sp: smin, smax = min(smin, min(sp)), max(smax, max(sp))
        nev = n
    print(f"fb {fb}, env {'open-loop square wave half-period %d' % ol if ol else 'eager [1,50]'}: {runs} runs; "
          f"runs with c != ph(M) somewhere: {bad}; runs violating the proved rate bounds: {rb if not ol else 'n/a'}; "
          f"min gap between c0 events: {wmin} steps (proved >= 135 under Back); "
          f"mean event spacing (2nd half) in [{smin:.1f}, {smax:.1f}] steps (proved long run [135, 171]); events per stage (last run) {nev}")
