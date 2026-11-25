#!/usr/bin/env python3
"""Shard B exploration (UNTRUSTED): under the SEQUENTIAL env (one pair), how close do the two
request rises at each gcd_hw arbiter (amerge op) come, over random per-node inertial delays?
Uses shard C's generated-netlist simulator (formal/tools/capwit3/simgen.py) read-only.
A near-tie (second request rising within W ticks of the first, the other low before) is the
shape ArbT.double_ack needs. usage: arbgap.py SPREAD|BASE:DEV NSEEDS a,b [a,b ...]"""
import os, sys, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "tools", "capwit3"))
import sim, simgen  # noqa: E402

def rises(xs):
    return [t for t in range(1, len(xs)) if xs[t] and not xs[t - 1]]

def main():
    spread, nseeds = sys.argv[1], int(sys.argv[2])
    base, sp = (int(v) for v in spread.split(":")) if ":" in spread else (1, int(spread))
    pairs = [tuple(int(v) for v in p.split(",")) for p in sys.argv[3:]]
    names, ops, out0, start = sim.load_net("gcd")
    arbs = [n for n, o in enumerate(ops) if o["k"] == "amerge"]
    best = {n: None for n in arbs}
    nruns = 0
    for (a, b) in pairs:
        for seed in range(nseeds):
            rng = random.Random(seed * 1000003 + a * 31 + b)
            dl = {}
            def delay(key):
                if key not in dl: dl[key] = rng.randint(base - sp, base + sp) if ":" in spread else (rng.randint(1, sp) if sp > 1 else 1)
                return dl[key]
            tr, P = simgen.simulate([a, b, 0], names, ops, delay=delay)
            nruns += 1
            for n in arbs:
                x, y = ops[n]["x"], ops[n]["y"]
                rx = rises([s[0][x] for s in tr]); ry = rises([s[0][y] for s in tr])
                for t1 in rx:
                    for t2 in ry:
                        g = abs(t1 - t2)
                        first, other = (x, y) if t1 <= t2 else (y, x)
                        tf = min(t1, t2)
                        if tr[tf - 1][0][other]:
                            continue   # other already high before: a waiter, not a race
                        if best[n] is None or g < best[n][0]:
                            best[n] = (g, a, b, seed, t1, t2)
    print(f"runs {nruns} (spread 1..{spread}, pairs {pairs})")
    for n in arbs:
        print(f"amerge op {n} ({names[ops[n]['z']]}): closest opposite rise gap", best[n])

if __name__ == "__main__":
    main()
