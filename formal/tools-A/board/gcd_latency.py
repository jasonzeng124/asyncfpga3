#!/usr/bin/env python3
"""gcd_latency.py (shard A, 2026-11-16; untrusted simulation): predicted gcd latency per input from the DECODED
bitstream, against the board's measurements (owner: "say how close the simulator is to the board").

    python3 gcd_latency.py MDIR BOARD.tsv OUT.tsv

MDIR: a formal/tools/margin/run.sh output dir for a gcd_ps-style build (net.simx, simx, net.json, bnd.json).
BOARD.tsv: research's cells/hw/gcd_cost_results.tsv (a b k ctzpre main ctzin result cycles latmin latmax; latency in
10 ns PS-timer cycles, harness included).
Each pair is simulated alone (sequential env, reset 400 ns, request at 401,000 ps) with EVERY arc at the prjxray
FAST_MIN (corner 0, class F) and at SLOW_MAX (corner 1, class S); kernel latency = out0 request rise - request rise.
Because every arc delay is a fixed fraction b of its [FAST_MIN, SLOW_MAX] band in research's draw model, and a run's
event order is the same at both ends only if no race flips, the latency at band position b is taken as the linear
interpolation lat(b) = lat_F + b (lat_S - lat_F) -- an approximation, stated. The board's cost model
(base + k, ctzpre, main, ctzin costs) is then fitted to the simulated latencies the same way research fitted the
board's, and the two sets of coefficients are printed side by side.
"""
import json, os, subprocess, sys
M, BT, OUT = sys.argv[1:4]
B = json.load(open(os.path.join(M, "bnd.json")))["boundary"]
N = json.load(open(os.path.join(M, "net.json")))["nodes"]; idx = {n: i for i, n in enumerate(N)}
cls = os.path.join(M, "empty_cls.json"); open(cls, "w").write('{"S": [], "F": []}')
rows = [l.split() for l in open(BT) if l.strip() and not l.startswith("a\t")]
def lat(a, b, corner, c):
    d = os.path.join(M, "lat_dump.json")
    r = subprocess.run([os.path.join(M, "simx"), os.path.join(M, "net.simx"), "--maxev", "2000000000", "--pairs", "%s,%s" % (a, b),
        "--kernel", "gcd", "--corner", str(corner), "--kappa", "0", "--classes", cls, "--cdefault", c, "--data0", "--full",
        "--R", "400000", "--su", "1000", "--datachange", "broad", "--nextreq", "seq", "--tmax", "100000000", "--dump", d],
        capture_output=True, text=True, env=dict(os.environ, KDEN="100"))
    ok = "RESULT OK" in r.stdout
    D = json.load(open(d))["nodes"]
    rq = D[str(idx[B["req"]])][1][0]; o = D[str(idx[B["out0_req"]])][1][0]
    return (o - rq) / 1000.0, ok
res = []
with open(OUT, "w") as f:
    f.write("a\tb\tk\tctzpre\tmain\tctzin\tboard_lat_ns\tsim_fastmin_ns\tsim_slowmax_ns\tok\n")
    for r in rows:
        a, b, k, cp, mn, ci = r[:6]; latmin = float(r[8]); latmax = float(r[9])
        lf, okf = lat(a, b, 0, "F"); ls, oks = lat(a, b, 1, "S")
        res.append((int(k), int(cp), int(mn), int(ci), (latmin + latmax) / 2 * 10, lf, ls))
        f.write("%s\t%s\t%s\t%s\t%s\t%s\t%.0f\t%.1f\t%.1f\t%s\n" % (a, b, k, cp, mn, ci, (latmin + latmax) / 2 * 10, lf, ls, okf and oks))
        print(a, b, "board %.0f ns" % ((latmin + latmax) / 2 * 10), "sim F %.1f S %.1f" % (lf, ls), okf, oks, flush=True)
X = [[1.0, k, cp, mn, ci] for k, cp, mn, ci, *_ in res]
def fit(y):
    """least squares by the normal equations (5 x 5, Gauss-Jordan; no numpy here)"""
    n = 5; A = [[sum(x[i] * x[j] for x in X) for j in range(n)] + [sum(x[i] * v for x, v in zip(X, y))] for i in range(n)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(A[r][c])); A[c], A[p] = A[p], A[c]
        for r in range(n):
            if r != c:
                f = A[r][c] / A[c][c]; A[r] = [u - f * w for u, w in zip(A[r], A[c])]
    return [A[i][n] / A[i][i] for i in range(n)]
cb = fit([r[4] for r in res]); cf = fit([r[5] for r in res]); cs = fit([r[6] for r in res])
names = ["base", "per k", "per pre-ctz", "per main", "per inner ctz"]
print("\ncoefficient       board(ns)  sim FAST_MIN  sim SLOW_MAX  b at which sim = board")
for i, n in enumerate(names):
    bb = (cb[i] - cf[i]) / (cs[i] - cf[i]) if cs[i] != cf[i] else float("nan")
    print("%-15s %9.1f %12.1f %12.1f %10.3f" % (n, cb[i], cf[i], cs[i], bb))
