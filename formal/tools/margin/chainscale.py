#!/usr/bin/env python3
"""margin/chainscale.py OUT/ --kernel K --pairs P.. --bands "bc,br,bx;bc,br,bx..." [--only REGEX] [--jobs N]
(shard C, 2026-11-18; UNTRUSTED simulation)

How much shorter could each matched delay be on THIS route? For one delay chain at a time (yosys instances
'<prefix>.chain.g[i].u...', found in routed.json), every arc along the chain -- each stage LUT's input pin from the previous
stage and the pip / hop gates between them, plus g[0]'s input arcs -- is scaled by a factor s in [0, 1] (an injection of
-(1-s) x the arc's delay at the given uniform bands, so no arc goes negative), and the run is repeated with no scatter. The
smallest s (bisected on a 1/16 grid) for which every band triple still returns the right answers is printed per chain:
s = 1.00 means the chain cannot be shortened at all at these corners; s = 0.40 means 60 % of it is unused here.
OUT/ = a run.sh output directory (net.json, routed.json, net.simx, simx, gclass.txt). A chain at s = 0 still has its
LUT cells' fixed site arcs outside the chain path; the number is about the chain's routed delay, not its cell count."""
import argparse, json, os, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
ap = argparse.ArgumentParser(); ap.add_argument("out"); ap.add_argument("--kernel", required=True)
ap.add_argument("--pairs", nargs="+", required=True); ap.add_argument("--bands", default="0.20,0.31,1.0;0.20,0.31,0.20")
ap.add_argument("--jobs", type=int, default=3); ap.add_argument("--only", default=None)
ap.add_argument("--maxev", default="300000000"); ap.add_argument("--tmax", default="1500000000")
a = ap.parse_args()
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); import kernels
if a.kernel in ("collatz", "collatz64"): a.pairs = ["%s,%s" % (p.split(",")[0], p.split(",")[0]) for p in a.pairs]
want = ",".join(str(v) for v in kernels.want(a.kernel, ["%d,%d" % tuple(int(t, 0) for t in p.split(",")) for p in a.pairs]))
O = a.out
cells = json.load(open(os.path.join(O, "routed.json")))["modules"]["top"]["cells"]
N = json.load(open(os.path.join(O, "net.json"))); G = N["gates"]; names = N["nodes"]; idx = {n: i for i, n in enumerate(names)}
GCL = {}
for l in open(os.path.join(O, "gclass.txt")): gi, c = l.split(); GCL[int(gi)] = c
drv = {g["out"]: (gi, g) for gi, g in enumerate(G)}
def lutnode(cellname):
    b = cells[cellname].get("attributes", {}).get("NEXTPNR_BEL", "")
    m = re.match(r"(SLICE_X\d+Y\d+)/([A-D])([56])LUT$", b)
    return "%s.%s%s" % m.groups() if m else None
chains = {}
for n in cells:
    m = re.match(r"^(.*)\.chain\.g\[(\d+)\]\.u", n)
    if m and (not a.only or re.search(a.only, m.group(1))):
        nd = lutnode(n)
        if nd and nd in idx: chains.setdefault(m.group(1), {})[int(m.group(2))] = idx[nd]
def arcd(gi, p, b):
    g = G[gi]; c = GCL.get(gi, "r"); bb = b[0] if c in "cq" else b[2] if c == "x" else b[1]
    e = g["arcs"][p]; return e["fmin"] + bb * (e["smax"] - e["fmin"])
def path_arcs(stages):
    """(gate index, pin) of every arc on the chain: g[0]'s inputs, and for i >= 1 the pin of g[i] whose source (through
    pip / hop copies) is g[i-1], with every pip / hop gate on that way."""
    out = []; order = [stages[k] for k in sorted(stages)]
    g0 = drv[order[0]][0]; out += [(g0, p) for p in range(len(G[g0]["ins"]))]
    for prev, cur in zip(order, order[1:]):
        gi = drv[cur][0]; found = False
        for p, u in enumerate(G[gi]["ins"]):
            hops = []; v = u
            for _ in range(300):
                if v == prev: break
                x = drv.get(v)
                if x is None or x[1].get("kind") not in ("pip", "hop"): v = None; break
                hops.append(x[0]); v = x[1]["ins"][0]
            if v == prev:
                out.append((gi, p)); out += [(h, 0) for h in hops]; found = True; break
        if not found: return None
    return out
BANDS = [tuple(float(x) for x in t.split(",")) for t in a.bands.split(";")]
def run(inj, b):
    f = os.path.join(O, "cs_%d_%d.json" % (os.getpid(), abs(hash((json.dumps(inj), b))) % 10**9))
    json.dump({"I": inj}, open(f, "w"))
    cmd = [os.path.join(O, "simx"), os.path.join(O, "net.simx"), "--periodic", "--maxev", a.maxev, "--kernel", a.kernel,
           "--want", want, "--pairs", *a.pairs, "--corner", "0", "--data0", "--full", "--R", "400000", "--su", "1000",
           "--datachange", "broad", "--nextreq", "seq", "--tmax", a.tmax, "--hostdelay", "12000", "--draw", "1",
           "--gclass", os.path.join(O, "gclass.txt"), "--bands", "%s,%s,%s" % b, "--sreg", "0", "--sarc", "0", "--w", "20", "--classes", f]
    r = subprocess.run(cmd, capture_output=True, text=True); os.remove(f)
    return "RESULT OK" in r.stdout
def ok_at(arcs, s):
    for b in BANDS:
        inj = [[names[G[gi]["out"]], p, -int((1 - s) * arcd(gi, p, b))] for gi, p in arcs]
        if not run(inj, b): return False
    return True
def one(item):
    pre, stages = item
    arcs = path_arcs(stages)
    if arcs is None: return pre, len(stages), None, "chain path not found"
    tot = {b: sum(arcd(gi, p, b) for gi, p in arcs) for b in BANDS}
    if not ok_at(arcs, 1.0): return pre, len(stages), None, "fails unscaled"
    lo, hi = 0, 16          # passes at hi/16; find the smallest k with a pass, assuming monotone
    if ok_at(arcs, 0.0): return pre, len(stages), 0.0, "%.0f ps" % max(tot.values())
    lo = 0
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if ok_at(arcs, mid / 16): hi = mid
        else: lo = mid
    return pre, len(stages), hi / 16, "%.0f ps" % max(tot.values())
print("# chainscale: bands %s; per chain: stages, smallest scale s still right at every band triple, chain path delay (max over bands)" % a.bands)
with ThreadPoolExecutor(a.jobs) as ex:
    rows = list(ex.map(one, sorted(chains.items())))
for pre, n, s, note in sorted(rows, key=lambda r: (r[2] is None, -(r[2] or 0))):
    print("%-58s %3d stages  s_min %s  %s" % (pre.replace("bridge_i.udut.", ""), n, "-" if s is None else "%.2f" % s, note))
