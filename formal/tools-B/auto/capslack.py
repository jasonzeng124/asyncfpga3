#!/usr/bin/env python3
"""tools-B/auto/capslack.py RUNDIR CELLREGEX EXP.txt --kernel K --pairs ... --seed S [--inject I.json] [--xband lo,hi]
(shard B, UNTRUSTED simulation): capture slack of the bd_link data latches whose yosys cell matches CELLREGEX, in one simx
run of research's draw S (the run draws.py makes, plus --dump). RUNDIR: a draws.py output dir with simx, net.simx, gclass.txt,
and net.json / routed.json beside them. For every latch LUT (a LUT that reads its own output) the enable pin is the input
driven (through pips) by a '.ctl.' cell, the data pins the other non-feedback inputs; from the LUT's INIT, the enable value
under which the output follows the data is 'transparent'. For every closing edge of the enable after reset, the slack is
the time from the data pin's last flip to the enable pin's closing flip, both at the LUT's pins (the LUT's own pin arcs,
tens of ps, are not included). Prints the smallest slacks and the number of closings with a data flip within 200 ps."""
import argparse, json, os, re, subprocess, sys, random
ap = argparse.ArgumentParser(); ap.add_argument("run"); ap.add_argument("cell"); ap.add_argument("exp")
ap.add_argument("--kernel", required=True); ap.add_argument("--pairs", nargs="+", required=True); ap.add_argument("--seed", type=int, required=True)
ap.add_argument("--inject"); ap.add_argument("--xband"); ap.add_argument("--tmax", default="400000000")
a = ap.parse_args(); O = a.run
want = ",".join(str(int(l.split()[0], 16)) for l in open(a.exp) if l.strip())
r = random.Random(7919 * a.seed + 17); c, q, x = r.uniform(.2, .31), r.uniform(.2, .31), r.uniform(.2, 1.0)
if a.xband: lo, hi = (float(v) for v in a.xband.split(",")); x = lo + (x - .2) / .8 * (hi - lo)
dump = os.path.join(O, "cap_%d.json" % os.getpid())
cmd = [os.path.join(O, "simx"), os.path.join(O, "net.simx"), "--periodic", "--maxev", "1000000000", "--want", want, "--hostdelay", "12000",
       "--pairs", *a.pairs, "--kernel", a.kernel, "--corner", "0", "--data0", "--full", "--R", "400000", "--su", "1000", "--datachange", "broad",
       "--nextreq", "seq", "--tmax", a.tmax, "--draw", str(a.seed), "--band", "0.38", "--sreg", "0.02", "--sarc", "0.126", "--regsize", "10",
       "--gclass", os.path.join(O, "gclass.txt"), "--bands", "%.6f,%.6f,%.6f" % (c, q, x), "--w", "20", "--dump", dump] + (["--classes", a.inject] if a.inject else [])
out = subprocess.run(cmd, capture_output=True, text=True)
print("# capslack seed %d bands %.3f,%.3f,%.3f%s: %s" % (a.seed, c, q, x, " +inject" if a.inject else "",
      next((l[:60] for l in (out.stdout + out.stderr).splitlines() if l.startswith("RESULT")), "no RESULT")))
D = json.load(open(dump))["nodes"]; os.remove(dump)
N = json.load(open(os.path.join(O, "net.json"))); G = N["gates"]
cells = json.load(open(os.path.join(O, "routed.json")))["modules"]["top"]["cells"]
bel = {v["attributes"].get("NEXTPNR_BEL"): k for k, v in cells.items()}
drv = {g["out"]: g for g in G}
def src(u):
    for _ in range(400):
        g = drv.get(u)
        if g is None or g["kind"] not in ("pip", "hop"): return u, g
        u = g["ins"][0]
    return u, None
def cellof(g):
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"]) if g else None
    return bel.get("%s/%s%sLUT" % m.groups(), "") if m else ""
def flips(n):
    v = D.get(str(n)); return v[1] if v else []
def val0(n):
    v = D.get(str(n)); return bool(v[0]) if v else False
rows = []
for g in G:
    if g["kind"] not in ("lut5", "lut6"): continue
    nm = cellof(g)
    if not re.search(a.cell, nm): continue
    k = len(g["ins"]); init = int(g["init"])
    srcs = [src(u) for u in g["ins"]]
    fb = [p for p, (s, h) in enumerate(srcs) if s == g["out"]]
    en = [p for p, (s, h) in enumerate(srcs) if ".ctl." in cellof(h)]
    if not fb or len(en) != 1: continue
    en = en[0]; dp = [p for p in range(k) if p not in fb and p != en and flips(g["ins"][p])]
    if not dp: continue
    f = lambda bits: (init >> sum(b << i for i, b in enumerate(bits))) & 1
    def follows(e):   # output depends on some data pin when enable = e
        for idx in range(1 << k):
            bits = [(idx >> i) & 1 for i in range(k)]
            if bits[en] != e: continue
            for p in dp:
                b2 = list(bits); b2[p] ^= 1
                if f(bits) != f(b2): return True
        return False
    tr = [e for e in (0, 1) if follows(e)]
    if len(tr) != 1: continue
    te = tr[0]; ef = flips(g["ins"][en]); ev = val0(g["ins"][en])
    closes = []
    for i, t in enumerate(ef):
        newv = ev ^ ((i + 1) & 1)
        if newv != te and t > 405000: closes.append(t)   # leaves the transparent value: the latch closes
    for p in dp:
        df = sorted(flips(g["ins"][p]))
        import bisect
        for t in closes:
            j = bisect.bisect_left(df, t)
            if j: rows.append((t - df[j - 1], nm, p, t))
rows.sort()
print("# %d closings x data pins on %d matching latch LUTs; within 200 ps: %d; within 500 ps: %d" % (len(rows), len({r[1] for r in rows}),
      sum(1 for r in rows if r[0] < 200), sum(1 for r in rows if r[0] < 500)))
for s, nm, p, t in rows[:8]: print("%7d ps  %s pin %d  close at %d" % (s, nm.replace("bridge_i.udut.", ""), p, t))
