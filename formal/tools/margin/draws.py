#!/usr/bin/env python3
"""margin/draws.py (shard C, UNTRUSTED): the board approximator. Many random draws of a build's delays, simulated on
the circuit decoded from its bitstream (simx --draw), and the fraction of draws that return the right answers.

    python3 draws.py NET.json BND.json OUT/ --kernel K --pairs a,b ... [--draws 64] [--seed0 1] [--w 20]
                     [--hostdelay 12000] [--band 0.38] [--sreg 0.16] [--sarc 0.126] [--regsize 10] [--jobs 8]

No adversary: every arc of every LUT pin (cell + its route, as decoded with prjxray's bands) takes
    d = (FAST_MIN + band * (SLOW_MAX - FAST_MIN)) * exp(sreg * N_region) * exp(sarc * N_arc)
N_region is one standard normal per die region (regsize x regsize slices, from the gate's SLICE site), N_arc one per
arc; both from a hash of the draw's seed (simx.cpp hash_n), so a draw is reproducible from (net, seed, parameters).
Defaults are research's fid GLS model (research/data/fid/f3_model.md, ring128_summary.md: GLS_SDF_BAND 0.38,
GLS_SCATTER_REGION 0.16 on 10x10 slices, GLS_SCATTER 0.126), sized there on the August ring data; lognormal factors as
gen.py's GLS_SCATTER_LOGN. Differences from research's GLS: the per-wire factor is per pin arc here (cell + route
together; the decoded net has no per-pip split), and the LUT model is formal's transport model with the H_RUNT(w) read
filter (w = 20 default) instead of research's metastability resolver. Start-up: formal's (reset, undriven = 0).
Host: --hostdelay ps after each acknowledge before the host moves data (12000 = one PS clock; the board's PS is slower).
Outcome per draw: PASS (RESULT OK), FAIL (wrong / missing / livelock found periodic), UNDECIDED (event cap, timeout).
"""
import argparse, math, os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__))
ap = argparse.ArgumentParser()
ap.add_argument("net"); ap.add_argument("bnd"); ap.add_argument("out")
ap.add_argument("--kernel", default="gcd"); ap.add_argument("--pairs", nargs="+", required=True)
ap.add_argument("--draws", type=int, default=64); ap.add_argument("--seed0", type=int, default=1)
ap.add_argument("--w", type=int, default=20); ap.add_argument("--hostdelay", type=int, default=12000)
ap.add_argument("--band", type=float, default=0.38); ap.add_argument("--sreg", type=float, default=0.16)
ap.add_argument("--sarc", type=float, default=0.126); ap.add_argument("--regsize", type=int, default=10)
ap.add_argument("--jobs", type=int, default=8); ap.add_argument("--tmax", type=int, default=25000000)
ap.add_argument("--model", default="research", choices=["research", "fid"],
                help="research: research's draw K (FOR-FORMAL 2026-11-16; bands per class from Random(7919K+17), region 0.02, "
                     "per-pip 0.126); fid: one band for all (--band), region --sreg, per-arc --sarc")
ap.add_argument("--routed", default=None, help="routed.json (research model: delay-chain cells by name)")
ap.add_argument("--inject", default=None, help="simx classes JSON with an 'I' list [[node, pin, ps], ..]: extra delay on those arcs (a negative control; not a model draw)")
ap.add_argument("--wallcap", type=int, default=1800); ap.add_argument("--maxev", default="100000000")
a = ap.parse_args()
os.makedirs(a.out, exist_ok=True)
if a.kernel in ("collatz", "collatz64"):
    # one-operand kernels: mk_bnd_sim.py maps the operand n into BOTH the a and b slots, so "n,0" would drive n = 0
    # (collatz(0) never ends). Research's gate hex gives "n 0": use n in both.
    a.pairs = ["%s,%s" % (p.split(",")[0], p.split(",")[0]) for p in a.pairs]
SIMX = os.path.join(a.out, "simx")
if not os.path.exists(SIMX) or os.path.getmtime(SIMX) < os.path.getmtime(os.path.join(HERE, "simx.cpp")):
    subprocess.run(["g++", "-O2", "-std=c++17", "-o", SIMX + ".%d" % os.getpid(), os.path.join(HERE, "simx.cpp")], check=True)
    os.replace(SIMX + ".%d" % os.getpid(), SIMX)
NETX = os.path.join(a.out, "net.simx")
if not os.path.exists(NETX) or os.path.getmtime(NETX) < max(os.path.getmtime(a.net), os.path.getmtime(a.bnd)):
    subprocess.run(["python3", os.path.join(HERE, "simx_conv.py"), a.net, a.bnd, NETX + ".%d" % os.getpid()], check=True)
    os.replace(NETX + ".%d" % os.getpid(), NETX)
GCL = None
if a.model == "research":
    import json, random
    if not a.routed: sys.exit("--model research needs --routed")
    if a.sreg == 0.16: a.sreg = 0.02            # research's region sigma (the fid default is 0.16)
    N = json.load(open(a.net)); G = N["gates"]
    cells = json.load(open(a.routed))["modules"]["top"]["cells"]
    bel = {c["attributes"].get("NEXTPNR_BEL"): n for n, c in cells.items() if c.get("attributes", {}).get("NEXTPNR_BEL")}
    cls = {}
    for gi, g in enumerate(G):
        if g["kind"] in ("carry", "muxf"): cls[gi] = "x"
        elif g["kind"] in ("lut6", "lut5"):
            m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"])
            nm = bel.get("%s/%s%sLUT" % (m.group(1), m.group(2), m.group(3)), "") if m else ""
            cls[gi] = "c" if ".chain.g[" in nm else "r"
    # pips / hops: 'q' (chain interconnect) if every LUT / cell they reach through pips and hops only is a chain LUT
    drv = {g["out"]: gi for gi, g in enumerate(G)}
    rd = {}
    for gi, g in enumerate(G):
        for i in g["ins"]: rd.setdefault(i, []).append(gi)
    memo = {}
    def sinks(gi, depth=0):
        if gi in memo: return memo[gi]
        memo[gi] = set()
        out = set()
        for r in rd.get(G[gi]["out"], []):
            if G[r]["kind"] in ("pip", "hop"):
                if depth < 400: out |= sinks(r, depth + 1)
            else: out.add(cls.get(r, "r"))
        memo[gi] = out; return out
    sys.setrecursionlimit(10000)
    for gi, g in enumerate(G):
        if g["kind"] in ("pip", "hop"):
            sk = sinks(gi); cls[gi] = "q" if sk == {"c"} else "p"
    GCL = os.path.join(a.out, "gclass.txt")
    with open(GCL, "w") as f:
        for gi in sorted(cls): f.write("%d %s\n" % (gi, cls[gi]))
    import collections
    print("draws: gate classes %s" % dict(collections.Counter(cls.values())), file=sys.stderr)
def bands(K):   # research's draw K: (b_c, b_r, b_cells) = Random(7919*K+17).uniform(.2,.31), (.2,.31), (.2,1.0)
    import random
    r = random.Random(7919 * K + 17); return (r.uniform(.2, .31), r.uniform(.2, .31), r.uniform(.2, 1.0))
want = []
if a.kernel != "gcd":
    sys.path.insert(0, HERE); import kernels
    want = ["--want", ",".join(str(v) for v in kernels.want(a.kernel, ["%d,%d" % tuple(int(t, 0) for t in p.split(",")) for p in a.pairs]))]

def run(seed):
    cmd = [SIMX, NETX, "--periodic", "--maxev", a.maxev] + want + ["--hostdelay", str(a.hostdelay),
           "--pairs", *a.pairs, "--kernel", a.kernel, "--corner", "0", "--data0", "--full", "--R", "400000", "--su", "1000",
           "--datachange", "broad", "--nextreq", "seq", "--tmax", str(a.tmax), "--draw", str(seed), "--band", str(a.band),
           "--sreg", str(a.sreg), "--sarc", str(a.sarc), "--regsize", str(a.regsize)] + (
           ["--gclass", GCL, "--bands", "%.6f,%.6f,%.6f" % bands(seed)] if GCL else []) + (["--classes", a.inject] if a.inject else []) + (["--w", str(a.w)] if a.w else [])
    t0 = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=a.wallcap)
    except subprocess.TimeoutExpired:
        return seed, "UNDECIDED", "timeout %d s" % a.wallcap, time.time() - t0, ""
    res = [l for l in r.stdout.splitlines() + r.stderr.splitlines() if l.startswith("RESULT")]
    per = re.search(r"PERIODIC P=(\d+) from (\d+)", r.stdout + r.stderr)
    ts = [int(m.group(1)) for m in re.finditer(r"^out0 #\d+ at (\d+) ps", r.stdout, re.M)]
    out0 = "last out0 at %d ps (%d answers)" % (ts[-1], len(ts)) if ts else "no out0"
    nm = re.search(r"^NEARMISS storage-output pulses < \d+ ps: (\d+); narrowest \(width, node, t\) \[\((\d+), '([^']*)', (\d+)\)", r.stderr, re.M)
    if nm: out0 += " [nearmiss %s; min %s ps at %s t=%s]" % nm.groups()
    for c in ("storage", "feeding-storage"):   # simx RACES=1: the closest input reordering that would flip a LUT
        rc = re.search(r"^RACES %s within \d+ ps: (\d+) events .*?closest \(gap, gate, pin, pin's source, t\) \[\((\d+), '([^']*)', (\d+), '([^']*)', (\d+)\)" % c, r.stderr, re.M)
        if rc: out0 += " [race %s %s ps at %s pin %s from %s t=%s; %s within window]" % ((c,) + rc.groups()[1:] + (rc.group(1),))
    if not res:
        return seed, "UNDECIDED", (r.stderr[-200:].replace("\n", " ") or "no RESULT (rc %d)" % r.returncode), time.time() - t0, ""
    if res[0].startswith("RESULT OK"):
        return seed, "PASS", res[0][:60], time.time() - t0, out0
    return seed, "FAIL", res[0] + (" [livelock P=%s from %s]" % per.groups() if per else ""), time.time() - t0, out0

seeds = list(range(a.seed0, a.seed0 + a.draws))
with ThreadPoolExecutor(a.jobs) as ex:
    rows = sorted(ex.map(run, seeds))
n = {k: sum(1 for r in rows if r[1] == k) for k in ("PASS", "FAIL", "UNDECIDED")}
dec = n["PASS"] + n["FAIL"]
def wilson(k, m, z=1.96):
    if m == 0: return (0.0, 1.0)
    p = k / m; d = 1 + z * z / m; c = p + z * z / (2 * m); h = z * math.sqrt(p * (1 - p) / m + z * z / (4 * m * m))
    return (max(0.0, (c - h) / d), min(1.0, (c + h) / d))
lo, hi = wilson(n["PASS"], dec)
with open(os.path.join(a.out, "draws.txt"), "w") as f:
    f.write("# board approximator (formal simx --draw; UNTRUSTED simulation): kernel %s pairs %s\n" % (a.kernel, " ".join(a.pairs)))
    if GCL: f.write("# model: RESEARCH draw K (bands per K: chain / rest U[.2,.31], CARRY4/F7/F8 U[.2,1]; region sigma %.3f on %dx%d slices (LUT/cell nodes only); per-pip sigma %.3f; lognormal); w %d; host %d ps after ack\n"
            % (a.sreg, a.regsize, a.regsize, a.sarc, a.w, a.hostdelay))
    else: f.write("# model: band %.3f, region sigma %.3f (%dx%d slices), arc sigma %.3f, lognormal; w %d; host %d ps after ack\n"
            % (a.band, a.sreg, a.regsize, a.regsize, a.sarc, a.w, a.hostdelay))
    for s, k, msg, dt, o in rows:
        f.write("%d %s %.1fs %s | %s\n" % (s, k, dt, o, msg))
with open(os.path.join(a.out, "draws_summary.txt"), "w") as f:
    f.write("draws %d: PASS %d FAIL %d UNDECIDED %d; pass fraction %.3f of decided (95%% Wilson %.3f-%.3f)\n"
            % (len(rows), n["PASS"], n["FAIL"], n["UNDECIDED"], (n["PASS"] / dec) if dec else float("nan"), lo, hi))
    tl = [int(re.search(r"at (\d+) ps", r[4]).group(1)) for r in rows if r[1] == "PASS" and "at " in r[4]]
    if tl: f.write("last answer (PASS draws): min %d mean %d max %d ps after t=0 (reset 400 ns included)\n" % (min(tl), sum(tl) // len(tl), max(tl)))
    f.write(("model: RESEARCH draw K (bands per K; --band unused), " if GCL else "") + "band %.3f sreg %.3f regsize %d sarc %.3f lognormal w %d host %d; seeds %d-%d\n"
            % (a.band, a.sreg, a.regsize, a.sarc, a.w, a.hostdelay, seeds[0], seeds[-1]))
    for s, k, msg, dt, o in rows:
        if k != "PASS": f.write("  seed %d %s %s\n" % (s, k, msg[:200]))
    nmw = sorted((int(m.group(1)), s, m.group(2)) for s, k, msg, dt, o in rows if k == "PASS"
                 for m in [re.search(r"min (\d+) ps at (\S+)", o)] if m)
    for c in ("storage", "feeding-storage"):
        rw = sorted((int(m.group(1)), s, k, m.group(2), m.group(3)) for s, k, msg, dt, o in rows
                    for m in [re.search(r"race %s (\d+) ps at (\S+) pin (\d+)" % c, o)] if m)
        if rw: f.write("closest %s races (gap ps, draw, verdict, LUT node, pin; informational): %s\n"
                       % (c, ", ".join("%d d%d %s %s p%s" % x for x in rw[:6])))
    if nmw: f.write("nearmiss (PASS draws, narrowest storage-output pulse; informational): %s\n"
                    % ", ".join("seed %d %d ps %s" % (s, w, n) for w, s, n in nmw[:5]))
print(open(os.path.join(a.out, "draws_summary.txt")).read(), end="")
