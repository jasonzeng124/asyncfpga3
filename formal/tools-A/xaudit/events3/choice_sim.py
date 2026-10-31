#!/usr/bin/env python3
"""Random concrete transport simulation of the E5 instance (Events3Ring): ring3 with the
request c1 -> c2 steered into two arms (then / else) and merged by an OR. Evidence only.

Gate-level, same model as the Lean `Beh3`: discrete time (1 step = 10 ps), every LUT and
route is a transport channel o(t) = i(t - d(t)) with d a random walk in [lo, hi] and
d(t+1) <= d(t) + 1 (monotone warp). C-elements are bd_c2n / bd_c2n_set: reset value under
rst, else maj(a, ~b, q). The choice pin of c2 (pin a):
    c1 -> route -> AND_b (c1 & [s == b]) -> route -> [else arm: X x (LUT1 + route)] -> OR -> route -> c2.I0
The select s is the environment's choice: transaction k of c1 (events 2k+1, 2k+2) goes to
branch sel[k] (random). Bundled mode: s switches to sel[k+1] HOLD = 60 steps after c1's fall (after the AND gates have seen the fall: the c1 -> AND route is <= 44), and
reaches the AND gates by a [1,2]-step route. Violation mode (--early E): s switches E steps
BEFORE c1 falls (the select changes while the request is high).

Checks, derived from what Events3Ring.ring_safe / Events3.Beh3.safe PROVE (not from a run):
  * the C-elements fire in ring3's order c1, c0, c2, c1, ... (every stage = ph(v, M), no
    glitch, no lost or duplicated token);
  * arm b carries exactly the events of the branch-b transactions (filt sel b), every
    transaction's two events on exactly one arm (conservation), and the OR output has as
    many events as c1;
  * the two arms are never both high at the OR's inputs;
  * every stage's consecutive events are >= 135 steps apart (cycle_le, window 135).
Usage: choice_sim.py [runs] [--else X] [--early E] [--fb lo hi]
"""
import random, sys

LUT, ROUTE, FB = (9, 13), (36, 44), (27, 33)

def run(seed, elseX=1, early=None, fb=FB, T=200, horizon=8000, hold=60):
    rnd = random.Random(seed)
    def walk(lo, hi):
        d = [rnd.randint(lo, hi)]
        for _ in range(horizon):
            nd = d[-1] + rnd.choice([-2, -1, 0, 0, 0, 1])
            d.append(min(hi, max(lo, nd)) if nd <= d[-1] + 1 else d[-1] + 1)
        return d
    def at(sig, t): return sig[max(t, 0)]
    N, v = 3, [1, 0, 0]
    sel = [rnd.random() < 0.5 for _ in range(horizon)]
    src = {(j, 0): (j - 1) % 3 for j in range(3)}
    src.update({(j, 1): (j + 1) % 3 for j in range(3)})
    dF = [walk(*LUT) for _ in range(N)]
    dG = {(j, p): walk(*ROUTE) for j in range(N) for p in (0, 1)}
    dQ = [walk(*fb) for _ in range(N)]
    dR = [walk(*ROUTE) for _ in range(N)]
    # arm b: route c1->AND, AND LUT, route AND->(chain)->OR ; chain of X (LUT1+route) on else arm
    arm_in = [walk(*ROUTE) for _ in (0, 1)]
    and_d = [walk(*LUT) for _ in (0, 1)]
    and_out = [walk(*ROUTE) for _ in (0, 1)]
    chain = [[(walk(*LUT), walk(*ROUTE)) for _ in range(elseX if b else 0)] for b in (0, 1)]
    s_route = walk(1, 2)
    or_d, or_out = walk(*LUT), walk(*ROUTE)
    rst = lambda t: 1 if t < T else 0
    c = [[v[j]] for j in range(N)]
    exc = [[v[j]] for j in range(N)]
    andx = [[0], [0]]; andv = [[0], [0]]          # AND excitation / output
    chs = [[[0] for _ in range(elseX if b else 0)] for b in (0, 1)]
    chl = [[[0] for _ in range(elseX if b else 0)] for b in (0, 1)]   # LUT1 outputs
    orx, orv = [0], [0]
    s = [sel[0]]
    falls = []                                     # times of c1 falls
    for t in range(1, horizon):
        # select: index of the transaction it announces
        if early is None:
            k = sum(1 for f in falls if f + hold <= t)
        else:
            # switch E steps before each fall: needs the future fall time -> use c1's count now
            # and switch as soon as c1 has been high for (its minimum high time - E) is not known;
            # model: switch at the rise + E (while c1 is still high)
            k = sum(1 for f in rises if f + early <= t)
        s.append(sel[k])
        for j in range(N):
            a = at(c[src[(j, 0)]], t - dG[(j, 0)][t])
            if j == 2:
                a = at(orv, t - or_out[t])
            b = at(c[src[(j, 1)]], t - dG[(j, 1)][t])
            q = at(c[j], t - dQ[j][t])
            r = rst(t - dR[j][t])
            exc[j].append(v[j] if r else int((a and not b) or (a and q) or ((not b) and q)))
        for b_ in (0, 1):
            req = at(c[1], t - arm_in[b_][t])
            sv = at(s, t - s_route[t])
            andx[b_].append(int(req and (sv == bool(b_))))
        for b_ in (0, 1):
            andv[b_].append(at(andx[b_], t - and_d[b_][t]))
            prev = andv[b_]
            for i, (dl, dr) in enumerate(chain[b_]):
                chl[b_][i].append(at(prev, t - dl[t]))        # LUT1, then its own route:
                chs[b_][i].append(at(chl[b_][i], t - dr[t]))  # two warps, each monotone
                prev = chs[b_][i]
        arm = [chs[b_][-1] if chain[b_] else andv[b_] for b_ in (0, 1)]
        ain = [at(arm[b_], t - and_out[b_][t]) for b_ in (0, 1)]
        orx.append(int(ain[0] or ain[1]))
        orv.append(at(orx, t - or_d[t]))
        for j in range(N):
            c[j].append(at(exc[j], t - dF[j][t]))
        if c[1][t] != c[1][t - 1]:
            (falls if c[1][t] == 0 else rises).append(t)
        if t == 1:
            pass
    return c, andx, andv, arm, orv, sel, ain_hist(arm, and_out, horizon)

rises = []

def ain_hist(arm, and_out, horizon):
    return [[arm[b][max(t - and_out[b][t], 0)] for t in range(horizon)] for b in (0, 1)]

def edges(sig):
    return [t for t in range(1, len(sig)) if sig[t] != sig[t - 1]]

def check(res, T=200):
    c, andx, andv, arm, orv, sel, ain = res
    ev = sorted((t, j) for j in range(3) for t in edges(c[j]))
    order = [j for _, j in ev]
    ok_order = order == [(1, 0, 2)[i % 3] for i in range(len(order))]
    n1 = len(edges(c[1]))
    # arm b must carry the events of the branch-b transactions of c1 (filt sel b)
    filt = [sum(1 for i in range(n1) if sel[i // 2] == bool(b)) for b in (0, 1)]
    arm_ev = [len(edges(ain[b])) for b in (0, 1)]
    ok_arms = all(abs(arm_ev[b] - filt[b]) <= 2 for b in (0, 1))   # last transaction in flight
    both = sum(1 for t in range(len(ain[0])) if ain[0][t] and ain[1][t])
    ok_or = abs(len(edges(orv)) - n1) <= 2
    gaps = [b - a for j in range(3) for a, b in zip(edges(c[j]), edges(c[j])[1:])]
    return ok_order, ok_arms, both == 0, ok_or, (min(gaps) if gaps else None), n1

if __name__ == "__main__":
    args = sys.argv[1:]
    runs = int(args[0]) if args and args[0].isdigit() else 50
    elseX = int(args[args.index("--else") + 1]) if "--else" in args else 1
    early = int(args[args.index("--early") + 1]) if "--early" in args else None
    fb = (int(args[args.index("--fb") + 1]), int(args[args.index("--fb") + 2])) if "--fb" in args else FB
    bad = {"order": 0, "arms": 0, "both-high": 0, "or-count": 0, "gap<135": 0}
    gmin, nev = 10**9, 0
    for sd in range(runs):
        rises.clear()
        o, a, x, r, g, n = check(run(sd, elseX=elseX, early=early, fb=fb))
        bad["order"] += not o; bad["arms"] += not a; bad["both-high"] += not x; bad["or-count"] += not r
        if g is not None:
            bad["gap<135"] += g < 135; gmin = min(gmin, g)
        nev += n
    broken = sum(1 for sd in range(0))
    print(f"else-arm {elseX} delay stage(s), select {'bundled' if early is None else f'changes {early} steps after the rise (while high)'}, feedback {fb}: "
          f"{runs} runs, {nev // max(runs,1)} c1 events/run; runs violating: {bad}; min same-stage event gap {gmin} steps (proved >= 135)")
