#!/usr/bin/env python3
"""margin/chainfix.py OUT/ --kernel K --pairs P.. --bands bc,br,bx [--extra PS] [--jobs N] (shard C, UNTRUSTED simulation)

Which matched delay is too short? For a run that fails in formal's simx (OUT/ = a run.sh output dir with net.json,
routed.json, net.simx, simx, gclass.txt), add EXTRA ps to one delay chain at a time (every input arc of the chain's first
LUT, g[0], an injection outside the prjxray band) and re-run with the given uniform bands and no scatter. A chain whose
lengthening turns the run into a PASS is a delay that is too short for this route; chains that change nothing are not.
Chains are found by name in routed.json (yosys instances '<prefix>.chain.g[0].u...'). Prints one line per chain."""
import argparse, json, os, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
ap = argparse.ArgumentParser(); ap.add_argument("out"); ap.add_argument("--kernel", required=True)
ap.add_argument("--pairs", nargs="+", required=True); ap.add_argument("--bands", default="0.25,0.25,0.6")
ap.add_argument("--extra", type=int, default=3000); ap.add_argument("--jobs", type=int, default=4)
ap.add_argument("--only", default=None, help="regex on the chain prefix"); ap.add_argument("--maxev", default="300000000"); ap.add_argument("--tmax", default="800000000")
a = ap.parse_args()
if a.extra <= 0: sys.exit("chainfix: --extra must be > 0 (a negative injection can make an arc's delay negative; simx does not guard it)")
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); import kernels
if a.kernel in ("collatz", "collatz64"): a.pairs = ["%s,%s" % (p.split(",")[0], p.split(",")[0]) for p in a.pairs]
want = ",".join(str(v) for v in kernels.want(a.kernel, ["%d,%d" % tuple(int(t, 0) for t in p.split(",")) for p in a.pairs]))
cells = json.load(open(os.path.join(a.out, "routed.json")))["modules"]["top"]["cells"]
N = json.load(open(os.path.join(a.out, "net.json"))); G = N["gates"]; names = N["nodes"]
node_of = {}
for n, c in cells.items():
    b = c.get("attributes", {}).get("NEXTPNR_BEL", "")
    m = re.match(r"(SLICE_X\d+Y\d+)/([A-D])([56])LUT$", b)
    if m: node_of[n] = "%s.%s%s" % m.groups()
groups = {}
for n in cells:
    m = re.match(r"^(.*)\.chain\.g\[0\]\.u", n)
    if m and n in node_of and (not a.only or re.search(a.only, m.group(1))): groups.setdefault(m.group(1), node_of[n])
kin = {names[g["out"]]: g["k"] for g in G}
def run(inj):
    f = os.path.join(a.out, "cf_%d.json" % (abs(hash(json.dumps(inj))) % 10**9))
    json.dump({"I": inj}, open(f, "w"))
    cmd = [os.path.join(a.out, "simx"), os.path.join(a.out, "net.simx"), "--periodic", "--maxev", a.maxev, "--kernel", a.kernel,
           "--want", want, "--pairs", *a.pairs, "--corner", "0", "--data0", "--full", "--R", "400000", "--su", "1000",
           "--datachange", "broad", "--nextreq", "seq", "--tmax", a.tmax, "--hostdelay", "12000", "--draw", "1",
           "--gclass", os.path.join(a.out, "gclass.txt"), "--bands", a.bands, "--sreg", "0", "--sarc", "0", "--w", "20", "--classes", f]
    r = subprocess.run(cmd, capture_output=True, text=True); os.remove(f)
    res = [l for l in (r.stdout + r.stderr).splitlines() if l.startswith("RESULT") or "MAXEV" in l]
    return re.sub(r"want \[[^]]*\] ", "", res[0])[:120] if res else "no verdict"
base = run([])
print("# chainfix: bands %s, +%d ps on one chain's g[0] at a time; base: %s" % (a.bands, a.extra, base))
def one(item):
    pre, nd = item
    return pre, nd, run([[nd, p, a.extra] for p in range(kin.get(nd, 1))])
with ThreadPoolExecutor(a.jobs) as ex:
    rows = list(ex.map(one, sorted(groups.items())))
for pre, nd, r in sorted(rows, key=lambda x: (not x[2].startswith("RESULT OK"), x[0])):
    print("%-6s %-60s %-18s %s" % ("FIXES" if r.startswith("RESULT OK") else "-", pre, nd, r))
