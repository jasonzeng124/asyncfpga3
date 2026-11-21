#!/usr/bin/env python3
"""tools-B/auto/decslack.py RUNDIR EXP.txt --kernel K --pairs ... --seed S [--xband lo,hi] (shard B, UNTRUSTED simulation):
research's N-way mux decode race in picoseconds, measured in one simx draw (as draws.py runs it, plus --dump). For every
decode LUT of every bdc_muxnN (a LUT read by a join <mux>.uj<k>.u; request pin = the pin shared by the mux's decodes
and positive in each, as tools-B/select/muxn_rows.py), and every rise of its request PIN (the pin node, after routing),
slack = rise time - the last flip of any index PIN before it (both at the LUT). Negative = the index moved after the
request arrived (the race research's rule E now sizes). Prints per mux the smallest slack and where."""
import argparse, json, os, re, subprocess, random, collections, bisect
ap = argparse.ArgumentParser(); ap.add_argument("run"); ap.add_argument("exp")
ap.add_argument("--kernel", required=True); ap.add_argument("--pairs", nargs="+", required=True); ap.add_argument("--seed", type=int, required=True)
ap.add_argument("--xband"); ap.add_argument("--tmax", default="400000000"); ap.add_argument("--w", default="20")
a = ap.parse_args(); O = a.run
want = ",".join(str(int(l.split()[0], 16)) for l in open(a.exp) if l.strip())
r = random.Random(7919 * a.seed + 17); c, q, x = r.uniform(.2, .31), r.uniform(.2, .31), r.uniform(.2, 1.0)
if a.xband: lo, hi = (float(v) for v in a.xband.split(",")); x = lo + (x - .2) / .8 * (hi - lo)
dump = os.path.join(O, "dec_%d.json" % os.getpid())
cmd = [os.path.join(O, "simx"), os.path.join(O, "net.simx"), "--periodic", "--maxev", "1000000000", "--want", want, "--hostdelay", "12000",
       "--pairs", *a.pairs, "--kernel", a.kernel, "--corner", "0", "--data0", "--full", "--R", "400000", "--su", "1000", "--datachange", "broad",
       "--nextreq", "seq", "--tmax", a.tmax, "--draw", str(a.seed), "--band", "0.38", "--sreg", "0.02", "--sarc", "0.126", "--regsize", "10",
       "--gclass", os.path.join(O, "gclass.txt"), "--bands", "%.6f,%.6f,%.6f" % (c, q, x), "--dump", dump] + (["--w", a.w] if a.w != "0" else [])
out = subprocess.run(cmd, capture_output=True, text=True)
res = next((l[:40] for l in (out.stdout + out.stderr).splitlines() if l.startswith("RESULT")), "no RESULT")
D = json.load(open(dump))["nodes"]; os.remove(dump)
G = json.load(open(os.path.join(O, "net.json")))["gates"]
cells = json.load(open(os.path.join(O, "routed.json")))["modules"]["top"]["cells"]
bel = {v["attributes"].get("NEXTPNR_BEL"): k for k, v in cells.items()}
drvg = {g["out"]: g for g in G}
def src(u):
    for _ in range(400):
        g = drvg.get(u)
        if g is None or g["kind"] not in ("pip", "hop"): return u
        u = g["ins"][0]
    return u
def cellof(g):
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"])
    return bel.get("%s/%s%sLUT" % m.groups(), "") if m else ""
reads = collections.defaultdict(set)
for g in G:
    if g["kind"] in ("lut5", "lut6"):
        for u in g["ins"]: reads[src(u)].add(cellof(g))
dec = collections.defaultdict(dict)
for g in G:
    if g["kind"] not in ("lut5", "lut6"): continue
    for rr in reads.get(g["out"], ()):
        m = re.match(r"^(.*)\.uj(\d+)\.u(\$LUT[56])?$", rr)
        if m and cellof(g).startswith(m.group(1) + ".") and ".uj" not in cellof(g): dec[m.group(1)][int(m.group(2))] = g
f = lambda g, ad: (int(g["init"]) >> ad) & 1
def support(g):
    k = len(g["ins"]); return [i for i in range(k) if any(f(g, ad) != f(g, ad ^ (1 << i)) for ad in range(1 << k))]
def positive(g, i):
    k = len(g["ins"]); return all(not f(g, ad) or (ad >> i) & 1 for ad in range(1 << k))
def hist(n):
    v = D.get(str(n)); return (bool(v[0]), v[1]) if v else (False, [])
print("# decslack seed %d bands %.3f,%.3f,%.3f: %s" % (a.seed, c, q, x, res))
for mux in sorted(dec):
    gs = dec[mux]; common = None
    for g in gs.values():
        s = {src(g["ins"][i]) for i in support(g) if positive(g, i)}; common = s if common is None else common & s
    best = None; nneg = 0; nr = 0
    for k, g in sorted(gs.items()):
        sup = support(g); rp = [i for i in sup if src(g["ins"][i]) in (common or set()) and positive(g, i)]
        if len(rp) != 1: continue
        v0, rf = hist(g["ins"][rp[0]])
        rises = [t for j, t in enumerate(rf) if (v0 ^ ((j + 1) & 1)) and t > 405000]
        idx = sorted(t for i in sup if i != rp[0] for t in hist(g["ins"][i])[1])
        for t in rises:
            j = bisect.bisect_right(idx, t)
            if not j: continue
            sl = t - idx[j - 1]; nr += 1
            # an index flip after the rise but before the request falls again is the race too
            jj = bisect.bisect_right(idx, t); fall = next((u for u in rf if u > t), None)
            if jj < len(idx) and fall is not None and idx[jj] < fall: sl = -(idx[jj] - t); nneg += 1
            if best is None or sl < best[0]: best = (sl, k, t)
    print("%s: %d request rises, %d with an index flip after the rise; smallest slack %s ps (input %s, t=%s)" %
          (mux.replace("bridge_i.udut.", ""), nr, nneg, best[0] if best else "-", best[1] if best else "-", best[2] if best else "-"))
