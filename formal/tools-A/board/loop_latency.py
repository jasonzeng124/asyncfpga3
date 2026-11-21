#!/usr/bin/env python3
"""loop_latency.py (shard A, 2026-11-17; untrusted simulation): per-iteration cost of a bench kernel predicted from the
DECODED bitstream, against the board's trip-count sweeps (research cells/hw/{loop_cost,xorshift_cost,trip_sweep}_results.tsv).

    python3 loop_latency.py MDIR KERNEL BOARD_SLOPE_NS "a,b:iters" ...

Each "a,b:iters" point is simulated alone (simx, sequential env, request at 401,000 ps) with every arc at FAST_MIN
(corner 0, class F) and at SLOW_MAX (corner 1, class S); kernel latency = out0 request rise - request rise. The
per-iteration cost at each band end is the least-squares slope of latency against iters; the band position at which
the simulated slope equals the board's is b = (board - F) / (S - F) (linear interpolation, stated as such).
"""
import json, os, subprocess, sys
M, K, BS = sys.argv[1], sys.argv[2], float(sys.argv[3])
pts = [(p.split(":")[0], int(p.split(":")[1])) for p in sys.argv[4:]]
B = json.load(open(os.path.join(M, "bnd.json")))["boundary"]
N = json.load(open(os.path.join(M, "net.json")))["nodes"]; idx = {n: i for i, n in enumerate(N)}
cls = os.path.join(M, "empty_cls.json"); open(cls, "w").write('{"S": [], "F": []}')
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools", "margin"))
import kernels
def lat(pair, corner, c):
    d = os.path.join(M, "loop_dump.json")
    want = ",".join(str(v) for v in kernels.want(K, [pair]))
    r = subprocess.run([os.path.join(M, "simx"), os.path.join(M, "net.simx"), "--maxev", "2000000000", "--want", want,
        "--pairs", pair, "--kernel", K, "--corner", str(corner), "--kappa", "0", "--classes", cls, "--cdefault", c,
        "--data0", "--full", "--R", "400000", "--su", "1000", "--datachange", "broad", "--nextreq", "seq",
        "--tmax", "100000000", "--dump", d], capture_output=True, text=True, env=dict(os.environ, KDEN="100"))
    if "RESULT OK" not in r.stdout:
        print("  FAIL", pair, corner, c, r.stdout.strip()[-150:], flush=True); return None
    D = json.load(open(d))["nodes"]
    return (D[str(idx[B["out0_req"]])][1][0] - D[str(idx[B["req"]])][1][0]) / 1000.0
def slope(xy):
    n = len(xy); sx = sum(x for x, _ in xy); sy = sum(y for _, y in xy)
    sxx = sum(x * x for x, _ in xy); sxy = sum(x * y for x, y in xy)
    return (n * sxy - sx * sy) / (n * sxx - sx * sx)
F, S = [], []
for p, it in pts:
    lf, ls = lat(p, 0, "F"), lat(p, 1, "S")
    print("%-22s iters %4d  sim FAST_MIN %9.1f ns  SLOW_MAX %9.1f ns" % (p, it, lf or -1, ls or -1), flush=True)
    if lf is not None: F.append((it, lf))
    if ls is not None: S.append((it, ls))
sf, ss = slope(F), slope(S)
print("\n%s per-iteration: board %.1f ns; sim FAST_MIN %.1f, SLOW_MAX %.1f; band position b = %.3f"
      % (K, BS, sf, ss, (BS - sf) / (ss - sf)))
