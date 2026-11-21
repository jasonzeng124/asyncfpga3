#!/usr/bin/env python3
"""exitcond_gcd_ce.py RESEARCH_CHECKOUT -- gcd's default graph vs its BDC_FE_EXITCOND graph (cmpi12: `d < 1` slt -> ult)
on inputs where the C's `a - b` overflows (undefined in C; LLVM's rewrite assumes it never happens). hsinterp.py,
in-order schedule, 400k-step limit. Prints each graph's status and `end` value per vector. Exit 1 if the graphs differ
on some vector (the expected outcome: (2147483647, -1) hangs in the default graph and returns -1 in the exitcond one)."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hsinterp  # noqa: E402
R = sys.argv[1] if len(sys.argv) > 1 else '.'
F = os.path.join(R, 'cloud/fixtures/%s/gcd/comp/handshake_transformed.mlir')
M = 1 << 32
diff = 0
for v in [(12, 18), (2147483647, -1), (-1, 2147483647), (1, -2147483647), (2147483647, -3)]:
    res = []
    for fx in ('frontend', 'frontend_exitcond'):
        r = hsinterp.Sim(open(F % fx).read()).run({'%arg0': v[0] % M, '%arg1': v[1] % M}, {}, limit=400000, seed=0)
        res.append((r['status'], r['ends'][0][0]))
    d = res[0] != res[1]; diff |= d
    print(f'{str(v):22s} default {res[0]}  exitcond {res[1]}  {"DIFFER" if d else "same"}')
sys.exit(1 if diff else 0)
