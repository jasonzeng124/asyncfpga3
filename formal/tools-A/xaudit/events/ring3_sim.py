#!/usr/bin/env python3
"""Random concrete transport simulation of the gate-level ring3 (scratch evidence for A-events).

Same model as the Lean `Beh`/`design_beh`: Discrete time (1 step = 10 ps), every LUT,
route, own-feedback and reset arc is a transport channel o(t) = i(f(t)) with f monotone
and t-hi <= f(t) <= t-lo (here f(t) = t - d(t), d a random walk in [lo,hi] with
d(t+1) <= d(t)+1, so the delay varies per event). LUT = bd_c2n / bd_c2n_set:
reset value under rst, else maj(a, ~b, q). Reset port falls at step T.

Checks against what EventsRing / EventsDesign.Ring3D.ring3_design PROVE (not against
a previous run): firing order c1, c0, c2, c1, ... (ring_inv), every hop gap in
[d, D] = [45, 57] steps once all reset arcs are low (T + 44), node period in
[270, 342] steps, and no other transition (no glitch).
Usage: ring3_sim.py [runs] [fb_lo fb_hi]   (default 200 runs, feedback [27,33])
"""
import random, sys

def run(seed, fb=(27, 33), lut=(9, 13), route=(36, 44), T=200, horizon=6000):
    rnd = random.Random(seed)
    def walk(lo, hi):
        d = [rnd.randint(lo, hi)]
        for _ in range(horizon):
            nd = d[-1] + rnd.choice([-2, -1, 0, 0, 0, 1])
            d.append(min(hi, max(lo, nd, 0)) if nd <= d[-1] + 1 else d[-1] + 1)
        return d
    N, v = 3, [1, 0, 0]
    src = {(j, 0): (j - 1) % 3 for j in range(3)}
    src.update({(j, 1): (j + 1) % 3 for j in range(3)})
    dF = [walk(*lut) for _ in range(N)]
    dG = {(j, p): walk(*route) for j in range(N) for p in (0, 1)}
    dQ = [walk(*fb) for _ in range(N)]
    dR = [walk(*route) for _ in range(N)]
    rst = lambda t: 1 if t < T else 0
    c = [[v[j]] for j in range(N)]           # c[j][t]
    exc = [[v[j]] for j in range(N)]
    def at(sig, t): return sig[max(t, 0)]
    for t in range(1, horizon):
        for j in range(N):
            s = t                              # exc at time t from pins at t
            a = at(c[src[(j, 0)]], s - dG[(j, 0)][s])
            b = at(c[src[(j, 1)]], s - dG[(j, 1)][s])
            q = at(c[j], s - dQ[j][s])
            r = rst(s - dR[j][s])
            e = v[j] if r else int((a and not b) or (a and q) or ((not b) and q))
            exc[j].append(e)
        for j in range(N):
            c[j].append(at(exc[j], t - dF[j][t]))
    return c

def check(c, T=200, d=45, D=57):
    ev = sorted((t, j) for j in range(3) for t in range(1, len(c[j])) if c[j][t] != c[j][t - 1])
    order = [j for _, j in ev]
    exp = [(1, 0, 2)[i % 3] for i in range(len(order))]
    ok_order = order == exp
    times = [t for t, _ in ev]
    gaps = [b - a for a, b in zip(times, times[1:])]
    first_ok = [g for t, g in zip(times, gaps) if t >= T + 44]
    per = [times[i + 3] - times[i] for i in range(len(times) - 3)]
    return ok_order, min(gaps) if gaps else None, max(first_ok) if first_ok else None, len(ev), per

if __name__ == "__main__":
    runs = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    fb = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (27, 33)
    bad, gmin, gmax, pmin, pmax = 0, 10**9, 0, 10**9, 0
    for s in range(runs):
        ok, lo, hi, n, per = check(run(s, fb=fb))
        if not ok or lo is None or lo < 45 or hi > 57:
            bad += 1
        else:
            gmin, gmax = min(gmin, lo), max(gmax, hi)
            pmin, pmax = min(pmin, min(p for p in per)), max(pmax, max(per))
    print(f"feedback {fb}: {runs} runs, {bad} violate the proved order/hop bounds; "
          f"hop gap observed [{gmin},{gmax}] steps (proved [45,57]); "
          f"node event spacing observed [{pmin},{pmax}] steps (proved [135,171])")
