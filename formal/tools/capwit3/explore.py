#!/usr/bin/env python3
"""C-witgen exploration (UNTRUSTED, not a proof): random inertial node delays.

explore.py K SEEDS [net]: every node (LUT output, chain stage, route) of the generated-level
gcd_hw network gets an inertial delay drawn uniformly from 1..K (per node, fixed per run);
the run is checked against every generated-level and lumped condition (simgen.gen_check +
sim.check). Prints, per seed, the violated condition tags and out0's closed values.
"""
import random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import simgen  # noqa: E402

K = int(sys.argv[1]); S = int(sys.argv[2]); net = sys.argv[3] if len(sys.argv) > 3 else "gcd"
vals = {"gcd": [12, 18, 0], "ipow": [3, 7, 0]}[net]
for seed in range(S):
    rnd = random.Random(seed); dl = {}
    def delay(key):
        if key not in dl: dl[key] = rnd.randint(1, K)
        return dl[key]
    names, ops, out0, start, tr, P, errs, falls = simgen.run(net, vals, delay=delay)
    tags = {}
    for e in errs:
        t = e[1] if isinstance(e[1], str) else e[0]
        tags[t] = tags.get(t, 0) + 1
    print(f"K={K} seed={seed}: {len(tr) - 1} ticks, out0 closes {[tr[e][3][out0] for e in falls]}, violations {tags}",
          flush=True)
