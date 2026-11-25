#!/usr/bin/env python3
"""Shard B copy (2026-11-08) of shard C's tools/huff/hazsweep.py with --kd (kappa = P/KD exactly, KDEN passed to
simadv.py) and --tmax; otherwise unchanged. Original doc: Shard C (UNTRUSTED): per-node skew adversary sweep. For every control storage node n (a logic gate reading its
own output through a copy chain, not latch-like: prep.py's classes), and for each of its live input pins p, one
run where pin p (its route hops and n's arc on p) is at the slow end (1+k) FAST_MAX and every other arc of the
circuit at the fast end (1-k) FAST_MIN (corner 0, kappa = P/25, transport). Reports runs whose result is wrong or
missing (counterexample candidates: check them with gatecheck/envcheck before believing them).
usage: hazsweep.py NET BND P OUT.txt [--jobs J] [--pairs ...] [--nodes N1 N2 ...]"""
import json, sys, os, subprocess, argparse, collections
from concurrent.futures import ThreadPoolExecutor
ap = argparse.ArgumentParser(); ap.add_argument("net"); ap.add_argument("bnd"); ap.add_argument("P", type=int); ap.add_argument("out")
ap.add_argument("--jobs", type=int, default=2); ap.add_argument("--pairs", nargs="+", default=["1071,462"])
ap.add_argument("--nodes", nargs="*", default=None); ap.add_argument("--default", default="F")
ap.add_argument("--w", type=int, default=0)
ap.add_argument("--kd", type=int, default=25); ap.add_argument("--tmax", default="3000000")
ap.add_argument("--fbonly", action="store_true", help="only each node's feedback pin(s)")
ap.add_argument("--control", action="store_true", help="only storage nodes that are not latch-like (prep.py)")
ap.add_argument("--mode", default="pin", choices=["pin", "allbutpin"])
a = ap.parse_args()
net = json.load(open(a.net)); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
BJ = json.load(open(a.bnd)); ENV = set(idx[x] for x in BJ["env"])
drv = {g["out"]: gi for gi, g in enumerate(G) if g["out"] not in ENV}
def is_copy(g): return g["k"] == 1 and g["init"] == 2
def chain(u):
    hops = []
    while u in drv and is_copy(G[drv[u]]): hops.append(u); u = G[drv[u]]["ins"][0]
    return u, hops
def dep(g, j):
    k, I = g["k"], g["init"]
    return any(((I >> x) & 1) != ((I >> (x ^ (1 << j))) & 1) for x in range(1 << k))
def latch_like(g, o):
    k, I = g["k"], g["init"]; ps = [chain(u)[0] for u in g["ins"]]
    fb = [j for j, s in enumerate(ps) if s == o and dep(g, j)]
    if not fb: return False
    fbj = fb[0]
    for p in range(k):
        if p == fbj or not dep(g, p) or ps[p] in ENV: continue
        for v in (0, 1):
            if all(((I >> x) & 1) == ((I >> (x ^ (1 << fbj))) & 1) for x in range(1 << k) if ((x >> p) & 1) == v):
                return True
    return False
cands = []
for gi, g in enumerate(G):
    if is_copy(g) or g["out"] in ENV or g["k"] < 2: continue
    o = g["out"]
    srcs = [chain(u) for u in g["ins"]]
    if not any(s == o for s, h in srcs): continue
    if a.control and latch_like(g, o): continue
    cands.append(o)
if a.nodes: cands = [idx[x] for x in a.nodes]
print("candidates", len(cands), file=sys.stderr)
W = os.environ.get("ADVW", "/tmp")
jobs = []
for o in cands:
    g = G[drv[o]]
    for p, u in enumerate(g["ins"]):
        if not dep(g, p): continue
        s, hops = chain(u)
        if s in ENV or N[s].endswith("_WIRE"): continue
        if a.fbonly and s != o: continue
        arcs = [[N[o], p]] + [[N[h], 0] for h in hops]
        jobs.append((N[o], p, N[s], arcs))
print("jobs", len(jobs), file=sys.stderr)
done = set()
if os.path.exists(a.out):
    for l in open(a.out):
        f = l.split()
        if len(f) > 2: done.add((f[0], int(f[1])))
def run(j):
    nm, p, s, arcs = j
    if (nm, p) in done: return None
    tag = "%s_%d" % (nm.replace("/", "_"), p)
    cf = "%s/hz_%s_%d.json" % (W, tag, os.getpid())
    if a.mode == "pin": cls = {"S": arcs, "F": []}
    json.dump(cls, open(cf, "w"))
    cmd = ["python3", os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools", "huff", "simadv.py"), a.net, a.bnd, "--pairs", *a.pairs,
           "--corner", "0", "--kappa", repr(a.P / a.kd), "--classes", cf, "--cdefault", a.default, "--data0", "--full",
           "--R", "400000", "--su", "1000", "--datachange", "broad", "--nextreq", "seq", "--tmax", a.tmax] + (["--w", str(a.w)] if a.w else [])
    r = subprocess.run(cmd, capture_output=True, text=True, env=dict(os.environ, KDEN=str(a.kd)))
    os.unlink(cf)
    res = [l for l in r.stdout.splitlines() if l.startswith("RESULT")]
    sl = [l for l in r.stderr.splitlines() if l.startswith("sim:") and "events" in l]
    return "%s %d %s %s | %s" % (nm, p, s, res[0] if res else "NORESULT " + r.stderr[-200:].replace("\n", " "), sl[-1] if sl else "")
with ThreadPoolExecutor(a.jobs) as ex, open(a.out, "a") as f:
    for line in ex.map(run, jobs):
        if line is None: continue
        f.write(line + "\n"); f.flush()
        if "RESULT OK" not in line: print(line, flush=True)
