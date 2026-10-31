#!/usr/bin/env python3
"""C-8z2: random bounded-delay runs of the gcd_hw gate network, looking for a deadlock
(H_NO_DEADLOCK' false) or a persistence violation (an excited gate that loses its excitation
before firing: a hazard, the only way a confluence argument could fail).

Semantics (the gate lists mirror Lean's `gatesE` = 8u's `gatesK ++ grantsK`, same order):
  * each gate, once excited toward v, draws a delay d in [1, D] and shows v d ticks later if
    still excited (bounded inertial delay; every BndG D obligation holds);
  * buses are the models' zero-delay functions; a link's latch holds while its `c` is low;
  * a/b sources free-running, `start` offers once (its LUT is exempt once it has offered);
  * a contested arbiter (both requests, no grant) is recorded and resolved at random.
Per run, up to the first out0 close: deadlock? persistence violations? contests? value = gcd?
Evidence only (finitely many schedules); proves nothing.

Usage: python3 -I persim.py NRUNS [D] [--mutant]
  --mutant2: negative control, the harness must report persistence violations: source a's
  bus takes a random value every tick (H_BUNDLE broken), so steer excitations flicker.
  --mutant: negative control, the harness must find a deadlock: start's token is withheld
  (the start LUT never fires), so the network must come to rest before out0 closes.
"""
import os, sys, math, random
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "formal", "tools", "capwit"))
import sim  # noqa: E402
from sim import ev, jval, sel2, selD, outs_of, NINT  # noqa: E402


def gates2(n, o):
    """[(key, excT, excF)] with key ('r', c) | ('a', c) | ('i', n, k)."""
    k = o["k"]; G = []
    R = lambda c: (lambda s: s.req[c]); A = lambda c: (lambda s: s.ack[c])
    I = lambda m: (lambda s: s.it[n][m])
    def wire(key, e): G.append((key, e, lambda s: not e(s)))
    def cel(key, e, f): G.append((key, lambda s: e(s) and f(s), lambda s: (not e(s)) and not f(s)))
    if k in ("forkG", "forkH"):
        i = o["i"]
        for c in o["os"]: wire(("r", c), R(i))
        G.append((("a", i), lambda s: all(s.ack[c] for c in o["os"]), lambda s: all(not s.ack[c] for c in o["os"])))
    elif k in ("join", "bjoin"):
        oo = o["o"]
        G.append((("r", oo), lambda s: all(s.req[i] for i in o["ins"]), lambda s: all(not s.req[i] for i in o["ins"])))
        for i in o["ins"]: wire(("a", i), A(oo))
    elif k in ("steerC", "steerD"):
        j, tc, fc = o["j"], o["t"], o["f"]
        wire(("r", tc), lambda s: s.req[j] and sel2(s.D[j]))
        wire(("r", fc), lambda s: s.req[j] and not sel2(s.D[j]))
        wire(("a", j), lambda s: s.ack[tc] or s.ack[fc])
    elif k == "mux":
        c, x, y, z = o["c"], o["x"], o["y"], o["z"]
        cel(("i", n, 0), R(x), lambda s: s.req[c] and not sel2(s.D[c]))
        cel(("i", n, 1), R(y), lambda s: s.req[c] and sel2(s.D[c]))
        wire(("r", z), lambda s: s.it[n][0] or s.it[n][1])
        cel(("a", x), I(0), A(z)); cel(("a", y), I(1), A(z)); wire(("a", c), A(z))
    elif k == "muxn":
        c, z, xs = o["c"], o["z"], o["xs"]
        for m in range(3): cel(("i", n, m), R(xs[m]), lambda s, m=m: s.req[c] and selD(s.D[c]) == m)
        wire(("r", z), lambda s: s.it[n][0] or s.it[n][1] or s.it[n][2])
        for m in range(3): cel(("a", xs[m]), I(m), A(z))
        wire(("a", c), A(z))
    elif k == "amerge":
        x, y, z = o["x"], o["y"], o["z"]
        G.append((("r", z), lambda s: (s.it[n][0] or s.it[n][1]) and not s.ack[x] and not s.ack[y],
                  lambda s: not (s.it[n][0] or s.it[n][1])))
        cel(("a", x), I(0), A(z)); cel(("a", y), I(1), A(z))
        G.append((("i", n, 0), lambda s: s.req[x] and not s.it[n][1] and not s.ack[z], lambda s: not s.req[x]))
        G.append((("i", n, 1), lambda s: s.req[y] and not s.it[n][0] and not s.ack[z], lambda s: not s.req[y]))
    elif k == "link":
        i, oo = o["i"], o["o"]
        wire(("i", n, 0), lambda s: (s.req[i] and not s.ack[oo]) or (s.it[n][0] and (s.req[i] or not s.ack[oo])))
        wire(("a", i), I(0)); wire(("r", oo), I(0))
    elif k == "src":
        z = o["z"]; wire(("r", z), lambda s: not s.ack[z])
    elif k == "sink":
        i = o["i"]; wire(("a", i), R(i))
    return G


class S:
    pass


def run(a, b, names, ops, out0, D, rng, mutant=False, tmax=400000, mutant2=False):
    NC = len(names)
    prod = {}
    for n, o in enumerate(ops):
        for c in outs_of(o): prod[c] = n
    pstart = prod[2]
    s = S()
    s.req = [False] * NC; s.ack = [False] * NC
    s.it = {n: [False] * NINT.get(o["k"], 0) for n, o in enumerate(ops)}
    latch = {o["o"]: 0 for o in ops if o["k"] == "link"}
    srcv = lambda w: a if w == 0 else (b if w == 1 else 0)
    if mutant2:   # negative control: source a's bus is not held (violates H_BUNDLE)
        srcv = lambda w: rng.randrange(64) if w == 0 else (b if w == 1 else 0)

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
                g = s.it[prod[c]]; won = g[1] or s.ack[o["y"]]
                v = 2 * (d(o["y"]) if won else d(o["x"])) + (1 if won else 0)
            elif k == "link": v = d(o["i"]) if s.it[prod[c]][0] else latch[c]
            elif k == "src": v = srcv(o["which"])
            memo[c] = v
            return v
        return [d(c) for c in range(NC)]

    GL = [(n, j, g) for n, o in enumerate(ops) for j, g in enumerate(gates2(n, o))]
    def get(key):
        return s.req[key[1]] if key[0] == "r" else (s.ack[key[1]] if key[0] == "a" else s.it[key[1]][key[2]])
    def put(key, v):
        if key[0] == "r": s.req[key[1]] = v
        elif key[0] == "a": s.ack[key[1]] = v
        else: s.it[key[1]][key[2]] = v

    s.D = dats()
    pend = {}          # gate index -> (target, fire time)
    started = False
    viol = []; contests = 0; rises = 0
    for t in range(tmax):
        # excitations at t
        exc = {}
        for gi, (n, j, (key, eT, eF)) in enumerate(GL):
            cur = get(key)
            if n == pstart and (started or mutant) and not s.req[2]:
                continue   # start's LUT never offers a 2nd token (mutant: never offers at all)
            if eT(s) and not cur: exc[gi] = True
            elif eF(s) and cur: exc[gi] = False
        for gi, (tv, ft) in list(pend.items()):
            if exc.get(gi) != tv:
                n, j, _ = GL[gi]
                viol.append((t, n, j, ops[n]["k"])); del pend[gi]
        if not exc and not pend:
            return dict(ok=False, why="deadlock", t=t, viol=viol, contests=contests)
        for gi, tv in exc.items():
            if gi not in pend: pend[gi] = (tv, t + rng.randint(1, D))
        for n, o in enumerate(ops):
            if o["k"] == "amerge" and not s.it[n][0] and not s.it[n][1] and s.req[o["x"]] and s.req[o["y"]] \
                    and not s.ack[o["z"]]:
                contests += 1
        fire = [gi for gi, (tv, ft) in pend.items() if ft <= t + 1]
        # arbiter exclusion: never raise both grants in one tick
        oldack = s.ack[out0]
        fired_g = {}
        for gi in fire:
            n, j, (key, _, _) = GL[gi]
            if key[0] == "i" and ops[n]["k"] == "amerge" and pend[gi][0]:
                fired_g.setdefault(n, []).append(gi)
        for n, gs in fired_g.items():
            if len(gs) == 2:
                drop = rng.choice(gs); fire.remove(drop); del pend[drop]
        for gi in fire:
            n, j, (key, _, _) = GL[gi]
            if n == pstart and not s.req[2] and pend[gi][0]: started = True
            put(key, pend[gi][0]); del pend[gi]
        for o in ops:
            if o["k"] == "link": latch[o["o"]] = s.D[o["o"]]
        s.D = dats()
        for o in ops:
            if o["k"] == "link": latch[o["o"]] = s.D[o["o"]]
        if oldack and not s.ack[out0]:
            return dict(ok=True, t=t + 1, val=s.D[out0], viol=viol, contests=contests)
    return dict(ok=False, why="tmax", viol=viol, contests=contests)


def main():
    nruns = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    D = int(sys.argv[2]) if len(sys.argv) > 2 and not sys.argv[2].startswith("-") else 4
    mutant = "--mutant" in sys.argv
    mutant2 = "--mutant2" in sys.argv
    names, ops, out0 = sim.load_net()
    rng0 = random.Random(8 * 1000 + D)
    fixed = [(12, 18), (0, 5), (7, 0), (0, 0), (1, 1), (35, 14), (2 ** 31 - 1, 2 ** 31 - 2),
             (1071, 462), (17, 5), (64, 48)]
    bad = 0; tot_v = 0; tot_c = 0
    for r in range(nruns):
        if r < len(fixed): a, b = fixed[r]
        else:
            w = rng0.choice([4, 8, 16, 31])
            a, b = rng0.randrange(2 ** w), rng0.randrange(2 ** w)
        res = run(a, b, names, ops, out0, D, random.Random(r * 7919 + D), mutant, mutant2=mutant2)
        tot_v += len(res["viol"]); tot_c += res["contests"]
        if res["ok"]:
            good = res["val"] == math.gcd(a, b)
            bad += 0 if good else 1
            print(f"run {r} a={a} b={b} D={D}: out0 closes t={res['t']} val={res['val']} "
                  f"{'=gcd' if good else '!=gcd'} persistence-violations={len(res['viol'])} contests={res['contests']}",
                  flush=True)
        else:
            bad += 1
            print(f"run {r} a={a} b={b} D={D}: {res['why'].upper()} at t={res.get('t')} "
                  f"persistence-violations={len(res['viol'])} {res['viol'][:3]}", flush=True)
    print(f"SUMMARY runs={nruns} D={D} mutant={mutant} mutant2={mutant2}: failures={bad} persistence-violations={tot_v} "
          f"contests={tot_c}")


if __name__ == "__main__":
    main()
