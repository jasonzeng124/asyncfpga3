#!/usr/bin/env python3
"""isprime_latency.py (shard A, 2026-11-17; untrusted simulation): isprime latency per n at FAST_MIN (corner 0, F) and SLOW_MAX
(corner 1, S) on a decoded bench build; kernels.py has no isprime, so the oracle is here (trial division, kernels/isprime).
    python3 isprime_latency.py MDIR n,n ...     (one operand: a and b share the bus, pass it twice)
"""
import json, os, subprocess, sys
M = sys.argv[1]; pts = sys.argv[2:]
B = json.load(open(M + "/bnd.json"))["boundary"]; N = json.load(open(M + "/net.json"))["nodes"]; idx = {n: i for i, n in enumerate(N)}
open(M + "/e.json", "w").write('{"S":[],"F":[]}')
def isprime(n):
    if n < 2: return 0
    d = 2
    while d * d <= n:
        if n % d == 0: return 0
        d += 1
    return 1
for p in pts:
    n = int(p.split(",")[0]); r = []
    for corner, c in ((0, "F"), (1, "S")):
        o = subprocess.run([M + "/simx", M + "/net.simx", "--maxev", "4000000000", "--want", str(isprime(n)), "--pairs", p, "--kernel", "isprime",
            "--corner", str(corner), "--kappa", "0", "--classes", M + "/e.json", "--cdefault", c, "--data0", "--full", "--R", "400000",
            "--su", "1000", "--datachange", "broad", "--nextreq", "seq", "--tmax", "2000000000", "--dump", M + "/d.json"],
            capture_output=True, text=True, env=dict(os.environ, KDEN="100"))
        if "RESULT OK" not in o.stdout: print(p, c, "FAIL", o.stdout[-200:]); r.append(None); continue
        D = json.load(open(M + "/d.json"))["nodes"]
        r.append((D[str(idx[B["out0_req"]])][1][0] - D[str(idx[B["req"]])][1][0]) / 1000)
    print(p, "want", isprime(n), "F %.1f S %.1f ns" % tuple(x or -1 for x in r), flush=True)
