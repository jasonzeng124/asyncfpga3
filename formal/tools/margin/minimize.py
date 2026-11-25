#!/usr/bin/env python3
"""margin/minimize.py (shard C, UNTRUSTED): shrink a failing row's slow-arc set to a minimal one that still fails.

    python3 minimize.py OUT/ NODE PIN KAPPA [--w 0] [--maxev 20000000] [--budget 400]

A cone row (CONES / STEER) slows hundreds of arcs at once, so the failure has no single pair of racing paths to name
(explain.py reports it UNRELIABLE or as a stall). This runs delta debugging (ddmin) on the row's slow arcs: a subset is
kept if the run with only that subset slowed still fails (any wrong / missing answer; same kappa, w, harness). The
result is 1-minimal (removing any single remaining chunk at the final granularity makes it pass) within --budget
simulations. It is written as a new row of OUT/margins.txt (pin 200 + the row's pin, same node), so that
`explain.py OUT NODE 200+PIN KAPPA` explains it as an ordinary race, and checkrows can check it.
"""
import argparse, json, os, re, subprocess, sys, time
ap = argparse.ArgumentParser(); ap.add_argument("out"); ap.add_argument("node"); ap.add_argument("pin", type=int); ap.add_argument("kappa")
ap.add_argument("--w", type=int, default=0); ap.add_argument("--maxev", default="20000000"); ap.add_argument("--budget", type=int, default=400)
a = ap.parse_args(); O = os.path.abspath(a.out)
row = None
for l in open(os.path.join(O, "margins.txt")):
    f = l.split()
    if len(f) > 4 and not l.startswith("#") and f[1] == a.node and f[2] == str(a.pin):
        if f[0] == "w=%d" % a.w: row = f; break           # the row of this w, else the first
        if row is None: row = f
if row is None: sys.exit("row not found")
S = [[x.rsplit("/", 1)[0], int(x.rsplit("/", 1)[1])] for x in row[-1].split(",")]
base = [l for l in open(os.path.join(O, "witness", "command.txt")) if not l.startswith("#")][0].split()
env = {}
while "=" in base[0] and not base[0].startswith("/"): k, v = base.pop(0).split("=", 1); env[k] = v
def setopt(cmd, opt, val):
    cmd = list(cmd)
    if opt in cmd: cmd[cmd.index(opt) + 1] = val
    else: cmd += [opt, val]
    return cmd
cf = os.path.join(O, "tmp", "min_%s_%d.json" % (a.node, a.pin)); os.makedirs(os.path.dirname(cf), exist_ok=True)
nsim = 0
def fails(sub):
    global nsim
    nsim += 1
    json.dump({"S": sub, "F": []}, open(cf, "w"))
    cmd = setopt(setopt(setopt(base, "--kappa", a.kappa), "--classes", cf), "--maxev", a.maxev)
    if "--w" in cmd: i = cmd.index("--w"); del cmd[i:i + 2]
    if a.w: cmd += ["--w", str(a.w)]
    if "--periodic" not in cmd: cmd += ["--periodic"]
    r = subprocess.run(cmd, capture_output=True, text=True, env=dict(os.environ, **env), cwd=O)
    res = [x for x in r.stdout.splitlines() if x.startswith("RESULT")]
    return bool(res) and not res[0].startswith("RESULT OK")
t0 = time.time()
if not fails(S): sys.exit("the full row does not fail at kappa %s w %d (nothing to minimise)" % (a.kappa, a.w))
n = 2
while len(S) >= 2 and nsim < a.budget:
    k = max(1, len(S) // n); chunks = [S[i:i + k] for i in range(0, len(S), k)]
    removed = False
    for c in chunks:
        rest = [x for x in S if x not in c]
        if rest and fails(rest):
            S = rest; n = max(n - 1, 2); removed = True; break
        if nsim >= a.budget: break
    if not removed:
        if n >= len(S): break
        n = min(2 * n, len(S))
print("minimised %d -> %d slow arcs in %d simulations (%.0f s)%s" % (len(row[-1].split(",")), len(S), nsim, time.time() - t0,
      "" if nsim < a.budget else "  (budget reached: not 1-minimal)"))
for x in S: print("  %s/%d" % tuple(x))
newpin = 200 + a.pin
line = "w=%-2d %s %d %s %s %s %s %s %s\n" % (a.w, a.node, newpin, row[3], a.kappa, "FAIL-min", "-", "minimised_from_pin_%d" % a.pin,
                                             ",".join("%s/%d" % (n_, p) for n_, p in S))
with open(os.path.join(O, "margins.txt"), "a") as f: f.write(line)
print("row added to margins.txt: %s %d (explain.py OUT %s %d %s --w %d)" % (a.node, newpin, a.node, newpin, a.kappa, a.w))
