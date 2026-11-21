#!/usr/bin/env python3
"""tools-B/auto/xdraws.py EXP.txt DRAWS_ARGS...  (shard B, UNTRUSTED simulation): shard C's margin/draws.py for a kernel
that margin/kernels.py does not know. EXP.txt holds one expected out0 per vector (hex, first field per line), in the order
of --pairs: research's oracle output (research/tools/suite/oracle.sh, compiled from kernels/K/K.c at run time -- derived
from the C, never recorded from a run). draws.py is run unchanged; only its `kernels.want` is replaced by this list.
Pass --kernel with any name other than gcd (simx uses it only to require --want)."""
import os, runpy, sys, types
exp = [int(l.split()[0], 16) for l in open(sys.argv[1]) if l.strip() and not l.startswith("//")]
mod = types.ModuleType("kernels")
def want(kernel, vecs):
    if len(vecs) != len(exp): raise SystemExit("xdraws: %d vectors but %d expected values" % (len(vecs), len(exp)))
    return list(exp)
mod.want = want; sys.modules["kernels"] = mod
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/margin/draws.py")
sys.argv = [D] + sys.argv[2:]
runpy.run_path(D, run_name="__main__")
