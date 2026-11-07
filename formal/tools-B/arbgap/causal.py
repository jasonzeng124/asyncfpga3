"""UNTRUSTED. Does the second request at an arbiter wait for the arbiter's own z.ack? Slow ONLY
the z.ack channel of that arbiter by D extra ticks (inertial) and see whether y.req's first rise moves."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "tools", "capwit3"))
import sim, simgen
names, ops, out0, start = sim.load_net("gcd")
def rises(xs): return [t for t in range(1, len(xs)) if xs[t] and not xs[t-1]]
for n in (171, 178, 180):
    o = ops[n]; x, y, z = o["x"], o["y"], o["z"]
    res = []
    for D in (1, 41):
        tr, P = simgen.simulate([12, 18, 0], names, ops, delay=lambda k, z=z, D=D: D if k == ("a", z) else 1)
        res.append((D, rises([s[0][x] for s in tr])[:2], rises([s[1][z] for s in tr])[:2], rises([s[0][y] for s in tr])[:2]))
    print("op", n, "(D, x.req rises, z.ack rises, y.req rises):", res)
