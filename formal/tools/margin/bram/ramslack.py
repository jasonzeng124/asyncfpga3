#!/usr/bin/env python3
"""margin/bram/ramslack.py MEMTASK_OUT K [--seed K0] [--xband lo,hi] [--hi PS] (shard C, UNTRUSTED simulation): how
much later a route's RAMs may put their data out before an answer or an array goes wrong -- the CAPTURE slack of the
RAM read path (DO against whatever samples it: a load's capture latch, or the consumer's own bundled request).
Every RAM's CLK -> DOADO arc (bram_gates.py role 0) gets +X ps (simx --classes "I", outside the band: a what-if), all
RAMs at once, on draw K of research's model (draws.py, via tools-B/auto/xdraws.py); bisection on X to 16 ps over
[0, --hi]. A CONSEQUENCE slack (later until a wrong result), an upper bound of the settle margin, like sideslack.py.
Prints the smallest failing X and the largest passing X."""
import argparse, json, os, re, subprocess, sys
ap = argparse.ArgumentParser(); ap.add_argument("out"); ap.add_argument("k")
ap.add_argument("--seed", type=int, default=10101); ap.add_argument("--xband", default="")
ap.add_argument("--hi", type=int, default=40000); a = ap.parse_args()
H = os.path.dirname(os.path.abspath(__file__)); B = os.path.join(H, "..", "..", "..", "tools-B", "auto")
O = os.path.abspath(a.out); M = os.path.join(O, "w", "m")
N = json.load(open(os.path.join(M, "net.json")))
nodes = N["nodes"]
I0 = [[nodes[g["out"]], g["ram"]["roles"].index(0)] for g in N["gates"] if g["kind"] == "ram"]
W = os.path.join(O, "ramslack"); os.makedirs(W, exist_ok=True)
pairs = open(os.path.join(O, "v", "pairs.txt")).read().split()
def run(x):
    inj = os.path.join(W, "inj_%d.json" % x)
    json.dump({"I": [[n, p, x] for n, p in I0]}, open(inj, "w"))
    env = dict(os.environ); env["DRAW_XBAND"] = a.xband
    d = os.path.join(W, "d")
    subprocess.run(["python3", os.path.join(B, "xdraws.py"), os.path.join(O, "v", "exp.txt"), os.path.join(M, "net.json"),
                    os.path.join(M, "bnd.json"), d, "--kernel", a.k, "--pairs", *pairs, "--draws", "1", "--seed0", str(a.seed),
                    "--jobs", "1", "--routed", os.path.join(M, "routed.json"), "--tmax", "1900000000",
                    "--mem", os.path.join(O, "v", "mem.txt"), "--inject", inj], env=env, capture_output=True, text=True)
    s = open(os.path.join(d, "draws_summary.txt")).read()
    ok = "PASS 1 " in s
    print("  +%d ps: %s" % (x, "PASS" if ok else "FAIL"), file=sys.stderr)
    return ok
if not run(0):
    sys.exit("ramslack: draw %d fails with no injection" % a.seed)
if run(a.hi):
    print("ramslack: draw %d%s passes even at +%d ps on every RAM's CLK->DO" % (a.seed, " xband " + a.xband if a.xband else "", a.hi)); sys.exit(0)
lo, hi = 0, a.hi
while hi - lo > 16:
    mid = (lo + hi) // 2
    if run(mid): lo = mid
    else: hi = mid
print("ramslack: draw %d%s: passes at +%d ps, fails at +%d ps on every RAM's CLK->DOADO (%d RAM output bits)"
      % (a.seed, " xband " + a.xband if a.xband else "", lo, hi, len(I0)))
