#!/usr/bin/env python3
"""margin/steermargin.py OUT/ CONDCELL --kernel K --pairs P.. [--bands b,b,b] (shard C, UNTRUSTED simulation)

The settle margin of a condition at the steers that read it: run simx (uniform bands, no scatter) with a dump; for every
LUT that reads the condition CONDCELL's output (through pip / hop copies), its request pins are the other live pins
whose source is a join or link control node (name has '_j.' or '.ctl.'). Arrival at a pin = the source's flip time + the
copy-chain and pin arcs at the corner the bands select (band 0 -> FAST_MIN, 1 -> SLOW_MAX, linear between; no region or
pip scatter, as simx --sreg 0 --sarc 0). For each request rise after reset: the gap since the condition's last arrival, and
whether the condition arrives again while that request is high (a live steer runt). Prints the smallest gaps per steer."""
import argparse, bisect, json, os, re, subprocess, sys
ap = argparse.ArgumentParser(); ap.add_argument("out"); ap.add_argument("cond"); ap.add_argument("--kernel", required=True)
ap.add_argument("--pairs", nargs="+", required=True); ap.add_argument("--bands", default="0,0,0")
ap.add_argument("--tmax", default="1500000000")
a = ap.parse_args()
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); import kernels, namelines
if a.kernel in ("collatz", "collatz64"): a.pairs = ["%s,%s" % (p.split(",")[0], p.split(",")[0]) for p in a.pairs]
want = ",".join(str(v) for v in kernels.want(a.kernel, ["%d,%d" % tuple(int(t, 0) for t in p.split(",")) for p in a.pairs]))
O = a.out; dump = os.path.join(O, "sm_%d.json" % os.getpid())
r = subprocess.run([os.path.join(O, "simx"), os.path.join(O, "net.simx"), "--periodic", "--maxev", "300000000", "--kernel", a.kernel,
    "--want", want, "--pairs", *a.pairs, "--corner", "0", "--data0", "--full", "--R", "400000", "--su", "1000", "--datachange",
    "broad", "--nextreq", "seq", "--tmax", a.tmax, "--hostdelay", "12000", "--draw", "1", "--gclass", os.path.join(O, "gclass.txt"),
    "--bands", a.bands, "--sreg", "0", "--sarc", "0", "--w", "20", "--dump", dump], capture_output=True, text=True)
print("# steermargin %s bands %s: %s" % (a.cond, a.bands, next((l[:40] for l in r.stdout.splitlines() if l.startswith("RESULT")), "no RESULT")))
D = json.load(open(dump))["nodes"]; os.remove(dump)
N = json.load(open(os.path.join(O, "net.json"))); G = N["gates"]; names = N["nodes"]
bel = namelines.belmap(os.path.join(O, "routed.json")); inv = {v: k for k, v in bel.items()}
GCL = {}
for l in open(os.path.join(O, "gclass.txt")): gi, c = l.split(); GCL[int(gi)] = c
bc, br, bx = (float(x) for x in a.bands.split(","))
drv = {g["out"]: (gi, g) for gi, g in enumerate(G)}
def arcd(gi, g, p):
    c = GCL.get(gi, "r"); b = bc if c in "cq" else bx if c == "x" else br
    e = g["arcs"][p]; return e["fmin"] + b * (e["smax"] - e["fmin"])
def chain(u):
    d = 0.0
    for _ in range(300):
        x = drv.get(u)
        if x is None: break
        gi, h = x
        if h.get("kind") not in ("pip", "hop"): break
        d += arcd(gi, h, 0); u = h["ins"][0]
    return u, d
def cell(node):
    m = re.match(r"(SLICE_X\d+Y\d+)\.([A-D])([56])$", node); return bel.get("%s/%s%sLUT" % m.groups(), node) if m else node
cn = [k for k in inv if re.search(a.cond, k)]
if not cn: sys.exit("no cell matches " + a.cond)
m = re.match(r"(SLICE_X\d+Y\d+)/([A-D])([56])LUT", inv[cn[0]]); cnode = names.index("%s.%s%s" % m.groups())
for gi, g in enumerate(G):
    if g.get("kind") not in ("lut5", "lut6"): continue
    src = [chain(u) for u in g["ins"]]
    cp = [p for p, (s, d) in enumerate(src) if s == cnode]
    if not cp or names[g["out"]] == names[cnode]: continue
    reqs = [p for p, (s, d) in enumerate(src) if re.search(r"_j\.|\.ctl\.", cell(names[s])) and D.get(str(s), [0, []])[1]]
    for q in cp:
        v0, h = D.get(str(src[q][0]), [False, []]); cd = sorted(t + src[q][1] + arcd(gi, g, q) for t in h)
        for p in reqs:
            rv0, rh = D.get(str(src[p][0]), [False, []]); dl = src[p][1] + arcd(gi, g, p)
            ev = [(t + dl, bool(rv0 ^ ((i + 1) & 1))) for i, t in enumerate(rh)]
            gaps, runts = [], 0
            for i, (t, up) in enumerate(ev):
                if not up or t < 405000: continue
                tf = next((x for x, u in ev[i + 1:] if not u), 1e18)
                k = bisect.bisect_right(cd, t)
                if k: gaps.append((round(t - cd[k - 1]), round(t)))
                if any(t < x < tf for x in cd): runts += 1
            gaps.sort()
            print("%s pin %d (request %s) vs pin %d (condition): %d requests, %d with the condition moving under them; smallest settle gaps %s ps (at t = %s ps)"
                  % (cell(names[g["out"]]), p, cell(names[src[p][0]]), q, len(gaps), runts, [x for x, _ in gaps[:5]], [y for _, y in gaps[:3]]))
