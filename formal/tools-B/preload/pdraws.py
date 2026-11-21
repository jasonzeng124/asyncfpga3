#!/usr/bin/env python3
"""tools-B/preload/pdraws.py (shard B, UNTRUSTED): shard C's board approximator (formal/tools/margin/draws.py, unchanged)
on a PRELOADED net, with the oracle from the same state.

    PRELOAD_I0=0x3ffffff0 python3 pdraws.py NET_PRELOADED.json BND.json OUT/ --kernel xorshift --pairs s,n ... [draws.py options]

draws.py computes the expected answers with margin/kernels.py from the pairs, which assumes the loop starts at 0. This
wrapper runs draws.py as is, but answers its `kernels.want` call with oracle.c (the kernel's C loop started from i0 =
PRELOAD_I0; compiled here from tools-B/preload/oracle.c). Everything else (simx, the delay model, the verdicts) is
draws.py's.
"""
import os, runpy, subprocess, sys, types
HERE = os.path.dirname(os.path.abspath(__file__))
I0 = os.environ.get("PRELOAD_I0")
if I0 is None: sys.exit("pdraws: set PRELOAD_I0")
ORC = os.path.join(os.environ.get("TMPDIR", "/tmp"), "preload_oracle_%d" % os.getpid())
subprocess.run(["gcc", "-O2", "-o", ORC, os.path.join(HERE, "oracle.c")], check=True)
def want(kernel, vecs):
    r = subprocess.run([ORC, kernel, I0] + vecs, capture_output=True, text=True)
    if r.returncode: sys.exit("pdraws: oracle refused: " + r.stderr.strip())
    return [int(v) for v in r.stdout.strip().split(",")]
m = types.ModuleType("kernels"); m.want = want; sys.modules["kernels"] = m
DR = os.path.join(HERE, "..", "..", "tools", "margin", "draws.py")
sys.argv = [DR] + sys.argv[1:]
try:
    runpy.run_path(DR, run_name="__main__")
finally:
    os.unlink(ORC)
