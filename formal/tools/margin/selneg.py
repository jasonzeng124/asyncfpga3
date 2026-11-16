#!/usr/bin/env python3
"""margin/selneg.py (shard C, UNTRUSTED): research's select negative controls (research/data/selneg/README.md) in formal's model.

    python3 selneg.py OUT/ KERNEL "PAIRS" MUX PS [PS ...]   e.g.  selneg.py OUT collatz "27,27 703,703" umux0 3000 6000

Research made a select race on purpose: the select latch's output arcs into ONE mux's request joins (MUX.uj0 / uj1) made
late by +PS in the SDF, same netlist. Here the same arcs (the join LUT's pin whose input comes from a select latch,
`lat.odd`) get +PS added to their prjxray delay (simx classes "I"; outside the band, so not a Spec behaviour), every
other arc at its fast-band minimum (kappa 0, corner 0: research's FAST_MIN column) and at the band midpoint, and the
kernel's answers are compared with the reference. A model that reproduces research's verdicts (fail where its gate
fails, pass where it passes) can stand in for that gate on this race; one that does not says which race it misses.
OUT is a margin run directory (net.json, net.simx, simx, witness/command.txt or any command, routed.json).
"""
import json, os, re, subprocess, sys
O, kernel, pairs, mux, pss = os.path.abspath(sys.argv[1]), sys.argv[2], sys.argv[3].split(), sys.argv[4], [int(x) for x in sys.argv[5:]]
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); import kernels
net = json.load(open(os.path.join(O, "net.json"))); G = net["gates"]; N = net["nodes"]
drv = {g["out"]: gi for gi, g in enumerate(G)}
R = json.load(open(os.path.join(O, "routed.json")))["modules"]["top"]["cells"]
cell_of = {}
for nm, c in R.items():
    b = c.get("attributes", {}).get("NEXTPNR_BEL")
    m = re.match(r"(SLICE_X\d+Y\d+)/([A-D])([56])LUT$", b or "")
    if m: cell_of["%s.%s%s" % m.groups()] = nm
node_of = {v: k for k, v in cell_of.items()}
idx = {n: i for i, n in enumerate(N)}
def is_copy(g): return g["k"] == 1 and g["init"] == 2
def src(u):
    while u in drv and is_copy(G[drv[u]]): u = G[drv[u]]["ins"][0]
    return u
inj = []
MODE = os.environ.get("SELNEG_MODE", "join")   # join: research's arcs (select latch -> MUX.uj0/uj1); data: select latch -> MUX's data LUTs
pat = r"\.%s\.uj[01]\b" % re.escape(mux) if MODE == "join" else r"\.%s\.udat\." % re.escape(mux)
for nm, nd in node_of.items():
    if not re.search(pat, nm) or nd not in idx: continue
    g = G[drv[idx[nd]]]
    for p, u in enumerate(g["ins"]):
        s = src(u); sc = cell_of.get(N[s], "")
        if "lat.odd" in sc: inj.append((nd, p, sc))
if not inj: sys.exit("no %s.uj0/uj1 pin fed by a select latch (lat.odd) found" % mux)
print("mode %s: %d arcs" % (MODE, len(inj)))
for nd, p, sc in inj[:6]: print("inject on %s pin %d (%s), fed by %s" % (nd, p, cell_of.get(nd), sc))
want = ",".join(str(v) for v in kernels.want(kernel, ["%d,%d" % tuple(int(t, 0) for t in p.split(",")) for p in pairs])) if kernel != "gcd" else None
TMAX = os.environ.get("TFULL", "25000000")
def run(ps, cdefault):
    cf = os.path.join(O, "tmp", "selneg.json"); os.makedirs(os.path.dirname(cf), exist_ok=True)
    json.dump({"S": [], "F": [], "I": [[nd, p, ps] for nd, p, _ in inj] if ps else []}, open(cf, "w"))
    cmd = [os.path.join(O, "simx"), os.path.join(O, "net.simx"), "--periodic", "--maxev", "100000000"] + (["--want", want] if want else []) + \
          ["--pairs", *pairs, "--kernel", kernel, "--corner", "0", "--kappa", "0", "--classes", cf, "--cdefault", cdefault, "--data0", "--full",
           "--R", "400000", "--su", "1000", "--datachange", "broad", "--nextreq", "seq", "--tmax", TMAX, "--hostdelay", os.environ.get("HOSTDELAY", "12000")]
    r = subprocess.run(cmd, capture_output=True, text=True, env=dict(os.environ, KDEN="100"), cwd=O)
    st = [x for x in r.stderr.splitlines() if x.startswith("sim:") and "events" in x or "injected" in x or "PERIODIC" in x]
    return ([x for x in r.stdout.splitlines() if x.startswith("RESULT")] or ["NO-VERDICT (event cap)"])[0] + "   [" + " | ".join(st[-3:]) + "]"
for cd, lab in (("F", "fast-band minimum (kappa 0)"), ("M", "band midpoint")):
    print("%s, no injection: %s" % (lab, run(0, cd)))
    for ps in pss: print("%s, +%d ps: %s" % (lab, ps, run(ps, cd)))
