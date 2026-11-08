#!/usr/bin/env python3
"""Shard B (UNTRUSTED), 2026-11-08: single-pin latch-HOLD adversary sweep on THE target.
The control sweeps of A and C (tools/huff/hazsweep.py --control) skip the 4,185 latch-like storage LUTs. A latch's
hold race is: its enable pin closes (slow) vs the next data reaching its data pin through the controller (fast).
For each latch L (out/target_ps_latch.json: pin e = enable), one run with L's enable-pin arc and the copy-chain hops
into that pin at the top of the window, (KD+P)/KD * FAST_MAX, and every other arc at the bottom, (KD-P)/KD *
FAST_MIN (corner 0, kappa = P/KD exactly, transport, H_RUNT(w) on LUT pins), via tools/huff/simadv.py.
Reports runs whose result is wrong or missing (candidates: check with gatecheck/envcheck before believing them).
usage: latchsweep.py NET BND LATCH.json P OUT.txt [--kd 100] [--w 20] [--jobs 4] [--pairs A,B ..] [--first N1 N2 ..]"""
import json, sys, os, subprocess, argparse
from concurrent.futures import ThreadPoolExecutor
ap = argparse.ArgumentParser(); ap.add_argument("net"); ap.add_argument("bnd"); ap.add_argument("lat")
ap.add_argument("P", type=int); ap.add_argument("out")
ap.add_argument("--kd", type=int, default=100); ap.add_argument("--w", type=int, default=20)
ap.add_argument("--jobs", type=int, default=4); ap.add_argument("--pairs", nargs="+", default=["1071,462"])
ap.add_argument("--first", nargs="*", default=[], help="latch names (net node names) to run first")
ap.add_argument("--only", nargs="*", default=None)
a = ap.parse_args()
net = json.load(open(a.net)); G = net["gates"]; N = net["nodes"]
drv = {g["out"]: gi for gi, g in enumerate(G)}
def is_copy(g): return g["k"] == 1 and g["init"] == 2
def nn(name):   # SLICE_X0Y47.ALUT.O6 -> SLICE_X0Y47.A6
    s, l, o = name.split(".")
    return "%s.%s%s" % (s, l[0], o[1])
rows = json.load(open(a.lat))["rows"]
jobs = []
for r in rows:
    q = r["q"]; g = G[drv[q]]; e = r["e"]
    hops = []; u = g["ins"][e]
    while u in drv and is_copy(G[drv[u]]): hops.append(u); u = G[drv[u]]["ins"][0]
    arcs = [[N[q], e]] + [[N[h], 0] for h in hops]
    jobs.append((N[q], e, N[u], arcs))
if a.only is not None: jobs = [j for j in jobs if j[0] in set(a.only)]
pri = {n: i for i, n in enumerate(a.first)}
jobs.sort(key=lambda j: pri.get(j[0], len(pri)))
done = set()
if os.path.exists(a.out):
    for l in open(a.out):
        f = l.split()
        if f: done.add(f[0])
W = os.environ.get("ADVW", "/tmp"); os.makedirs(W, exist_ok=True)
SIM = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools", "huff", "simadv.py")
print("jobs", len(jobs), "done", len(done), file=sys.stderr)
def run(j):
    nm, p, s, arcs = j
    if nm in done: return None
    cf = "%s/ls_%s_%d.json" % (W, nm.replace("/", "_"), os.getpid())
    json.dump({"S": arcs, "F": []}, open(cf, "w"))
    cmd = ["python3", SIM, a.net, a.bnd, "--pairs", *a.pairs, "--corner", "0", "--kappa", repr(a.P / a.kd),
           "--classes", cf, "--cdefault", "F", "--data0", "--full", "--R", "400000", "--su", "1000",
           "--datachange", "broad", "--nextreq", "seq", "--tmax", "3000000"] + (["--w", str(a.w)] if a.w else [])
    r = subprocess.run(cmd, capture_output=True, text=True, env=dict(os.environ, KDEN=str(a.kd)))
    os.unlink(cf)
    res = [l for l in r.stdout.splitlines() if l.startswith("RESULT")]
    sl = [l for l in r.stderr.splitlines() if l.startswith("sim:") and "events" in l]
    hr = [l for l in (r.stdout + r.stderr).splitlines() if "HRUNT" in l or "INFEAS" in l]
    line = "%s %d %s %s %s | %s" % (nm, p, s, res[0] if res else "NORESULT rc=%d %s" % (r.returncode, r.stderr[-300:].replace("\n", " ")),
                                   hr[0] if hr else "", sl[0] if sl else "")
    with open(a.out, "a") as f: f.write(line + "\n")
    return line
with ThreadPoolExecutor(a.jobs) as ex:
    for l in ex.map(run, jobs):
        if l and "RESULT OK" not in l: print(l, flush=True)
