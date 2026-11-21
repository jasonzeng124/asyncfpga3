#!/usr/bin/env python3
"""margin/sideslack.py OUT/ CELLREGEX --kernel K --pairs P.. [--bands bc,br,bx] [--hi PS] (shard C, UNTRUSTED simulation)

The slack of a named race in ps: add X ps to every input arc of the LUTs whose routed yosys instance matches CELLREGEX
(the slow side of the race, e.g. a compare's last LUT), uniform bands, no scatter, and bisect the smallest X at which the
run (which must pass at X = 0) fails, to 25 ps. X is an injection outside the prjxray band: the result reads "this side
may arrive X ps later before the run breaks", at those bands."""
import argparse, json, os, re, subprocess, sys
ap = argparse.ArgumentParser(); ap.add_argument("out"); ap.add_argument("cells"); ap.add_argument("--kernel", required=True)
ap.add_argument("--pairs", nargs="+", required=True); ap.add_argument("--bands", default="0.25,0.25,0.6")
ap.add_argument("--hi", type=int, default=8000); ap.add_argument("--maxev", default="300000000"); ap.add_argument("--tmax", default="1500000000")
a = ap.parse_args()
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); import kernels
if a.kernel in ("collatz", "collatz64"): a.pairs = ["%s,%s" % (p.split(",")[0], p.split(",")[0]) for p in a.pairs]
want = ",".join(str(v) for v in kernels.want(a.kernel, ["%d,%d" % tuple(int(t, 0) for t in p.split(",")) for p in a.pairs]))
cells = json.load(open(os.path.join(a.out, "routed.json")))["modules"]["top"]["cells"]
N = json.load(open(os.path.join(a.out, "net.json"))); kin = {N["nodes"][g["out"]]: g["k"] for g in N["gates"]}
nodes = []
for n, c in cells.items():
    m = re.match(r"(SLICE_X\d+Y\d+)/([A-D])([56])LUT$", c.get("attributes", {}).get("NEXTPNR_BEL", ""))
    if m and re.search(a.cells, n): nodes.append(("%s.%s%s" % m.groups(), n))
if not nodes: sys.exit("no LUT matches %s" % a.cells)
def run(x):
    f = os.path.join(a.out, "ss_%d.json" % os.getpid())
    json.dump({"I": [[nd, p, x] for nd, _ in nodes for p in range(kin.get(nd, 1))] if x else []}, open(f, "w"))
    cmd = [os.path.join(a.out, "simx"), os.path.join(a.out, "net.simx"), "--periodic", "--maxev", a.maxev, "--kernel", a.kernel,
           "--want", want, "--pairs", *a.pairs, "--corner", "0", "--data0", "--full", "--R", "400000", "--su", "1000",
           "--datachange", "broad", "--nextreq", "seq", "--tmax", a.tmax, "--hostdelay", "12000", "--draw", "1",
           "--gclass", os.path.join(a.out, "gclass.txt"), "--bands", a.bands, "--sreg", "0", "--sarc", "0", "--w", "20", "--classes", f]
    r = subprocess.run(cmd, capture_output=True, text=True); os.remove(f)
    return "RESULT OK" in r.stdout
print("# sideslack: %d LUTs match %s: %s" % (len(nodes), a.cells, ", ".join(n for _, n in nodes[:4])))
if not run(0): sys.exit("fails at X = 0 (bands %s): no slack to measure" % a.bands)
lo, hi = 0, a.hi
if run(hi): print("bands %s: passes at +%d ps (slack > %d)" % (a.bands, hi, hi)); sys.exit()
while hi - lo > 25:
    mid = (lo + hi) // 2
    if run(mid): lo = mid
    else: hi = mid
print("bands %s: passes at +%d ps, fails at +%d ps -> slack %d-%d ps" % (a.bands, lo, hi, lo, hi))
