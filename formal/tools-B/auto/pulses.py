#!/usr/bin/env python3
"""tools-B/auto/pulses.py RUNDIR CELLREGEX EXP.txt --kernel K --pairs ... --seed S [--xband lo,hi] [--w W] [--below PS]
(shard B, UNTRUSTED simulation): output pulses of the LUTs whose yosys cell matches CELLREGEX (ANY LUT, combinational or
storage: simx's NEARMISS sees only storage outputs) in one simx run of research's draw S, run as draws.py runs it plus
--dump. RUNDIR: a draws.py output dir (simx, net.simx, gclass.txt) with net.json / routed.json beside it. A pulse = two
consecutive output flips after reset release + 5 ns; prints every pulse narrower than --below (default 1000 ps) with its
cell, width and time, and per cell the number of flips. --w (default 20, draws.py's) is simx's H_RUNT filter width."""
import argparse, json, os, re, subprocess, random, collections
ap = argparse.ArgumentParser(); ap.add_argument("run"); ap.add_argument("cell"); ap.add_argument("exp")
ap.add_argument("--kernel", required=True); ap.add_argument("--pairs", nargs="+", required=True); ap.add_argument("--seed", type=int, required=True)
ap.add_argument("--xband"); ap.add_argument("--tmax", default="400000000"); ap.add_argument("--w", default="20"); ap.add_argument("--below", type=int, default=1000)
a = ap.parse_args(); O = a.run
want = ",".join(str(int(l.split()[0], 16)) for l in open(a.exp) if l.strip())
r = random.Random(7919 * a.seed + 17); c, q, x = r.uniform(.2, .31), r.uniform(.2, .31), r.uniform(.2, 1.0)
if a.xband: lo, hi = (float(v) for v in a.xband.split(",")); x = lo + (x - .2) / .8 * (hi - lo)
dump = os.path.join(O, "pul_%d.json" % os.getpid())
cmd = [os.path.join(O, "simx"), os.path.join(O, "net.simx"), "--periodic", "--maxev", "1000000000", "--want", want, "--hostdelay", "12000",
       "--pairs", *a.pairs, "--kernel", a.kernel, "--corner", "0", "--data0", "--full", "--R", "400000", "--su", "1000", "--datachange", "broad",
       "--nextreq", "seq", "--tmax", a.tmax, "--draw", str(a.seed), "--band", "0.38", "--sreg", "0.02", "--sarc", "0.126", "--regsize", "10",
       "--gclass", os.path.join(O, "gclass.txt"), "--bands", "%.6f,%.6f,%.6f" % (c, q, x), "--dump", dump] + (["--w", a.w] if a.w != "0" else [])
out = subprocess.run(cmd, capture_output=True, text=True)
print("# pulses seed %d bands %.3f,%.3f,%.3f w %s: %s" % (a.seed, c, q, x, a.w,
      next((l[:60] for l in (out.stdout + out.stderr).splitlines() if l.startswith("RESULT")), "no RESULT")))
D = json.load(open(dump))["nodes"]; os.remove(dump)
G = json.load(open(os.path.join(O, "net.json")))["gates"]
cells = json.load(open(os.path.join(O, "routed.json")))["modules"]["top"]["cells"]
bel = {v["attributes"].get("NEXTPNR_BEL"): k for k, v in cells.items()}
def cellof(g):
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"])
    return bel.get("%s/%s%sLUT" % m.groups(), "") if m else ""
rows, nfl = [], collections.Counter()
for g in G:
    if g["kind"] not in ("lut5", "lut6"): continue
    nm = cellof(g)
    if not nm or not re.search(a.cell, nm): continue
    v = D.get(str(g["out"])); fl = v[1] if v else []
    nfl[nm] = len(fl)
    for i in range(1, len(fl)):
        if fl[i - 1] < 405000: continue
        w = fl[i] - fl[i - 1]
        if w < a.below: rows.append((w, nm, fl[i - 1]))
rows.sort()
print("# %d matching LUTs, %d pulses < %d ps" % (len(nfl), len(rows), a.below))
for w, nm, t in rows[:40]: print("%7d ps  t=%d  %s" % (w, t, nm))
for nm, n in sorted(nfl.items()):
    if n: print("# flips %5d  %s" % (n, nm))
