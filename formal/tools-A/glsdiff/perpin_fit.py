#!/usr/bin/env python3
"""perpin_fit.py -- does the fid GLS LUT equal "per-pin transport, then the zero-time
function" (Lean: each pin a Pure channel with lo = hi = its arc, LUT = Kleene function
of the delayed pins, as in Formal/Core/XAudit/Events2Pin)?
XOR(A1,A2), arcs 100 / 150 ps, random edge traces (gaps 1..400 ps).
Usage: python3 -I perpin_fit.py PRIMS_V N  [--carry]   (--carry: CARRY4 S0->O0 instead)"""
import os, random, subprocess, sys, tempfile, importlib.util
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("cf", os.path.join(here, "..", "gls-compare", "channel_fit.py"))
cf = importlib.util.module_from_spec(spec); spec.loader.exec_module(cf)
D = {1: 100, 2: 150}
def ref(edges):
    ev = sorted([(t + D[p], p, v) for t, p, v in edges])
    a = {1: 0, 2: 0}; f = 0; out = []
    for t, p, v in ev:
        a[p] = v; nf = a[1] ^ a[2]
        if nf != f:
            if out and out[-1][0] == t: out.pop()      # same-ps zero-width glitch
            else: out.append((t, nf))
            f = nf
    return out
def main():
    prims, n = sys.argv[1], int(sys.argv[2])
    rng = random.Random(5); ok = 0; first = None
    with tempfile.TemporaryDirectory() as wd:
        for k in range(n):
            t = 1000; edges = []; a = {1: 0, 2: 0}
            for _ in range(rng.randint(3, 12)):
                t += rng.randint(1, 400); p = rng.choice((1, 2)); a[p] ^= 1; edges.append((t, p, a[p]))
            got = [(tt, 1 if v == "1" else 0) for tt, v in cf.run_iverilog(prims, cf.make_tb(edges, 2, None), wd)]
            exp = ref(edges)
            if got == exp: ok += 1
            elif first is None: first = (edges, got, exp)
    print("per-pin transport: %d/%d exact" % (ok, n))
    if first: print("first mismatch:\n  in  %s\n  gls %s\n  ref %s" % first)
main()
