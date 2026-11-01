import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "tools", "capwit3"))
import sim, simgen
names, ops, out0, start = sim.load_net("gcd")
tr, P = simgen.simulate([12, 18, 0], names, ops)
def ev(c, comp):
    xs = [s[comp][c] for s in tr]
    return [(t, xs[t]) for t in range(1, len(xs)) if xs[t] != xs[t-1]]
for n in (171, 178, 180):
    o = ops[n]; x, y, z = o["x"], o["y"], o["z"]
    print("op", n, "x", names[x], "y", names[y], "z", names[z])
    for lab, c, comp in (("x.req", x, 0), ("x.ack", x, 1), ("y.req", y, 0), ("y.ack", y, 1), ("z.req", z, 0), ("z.ack", z, 1)):
        print("  ", lab, ev(c, comp)[:8])
