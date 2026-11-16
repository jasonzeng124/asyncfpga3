#!/usr/bin/env python3
"""margin/tcut.py (shard C, UNTRUSTED): WHEN a failing row's slow arcs do their damage, and which transition does it.

    python3 tcut.py OUT/ NODE PIN KAPPA [--w 0] [--routed ROUTED.json]

A cone / steer row (or a minimised one, pin 200+) slows many arcs; its failure can surface microseconds after the
first divergence, at a storage LUT that only receives the damage (explain.py then reports INCONSISTENT or no race).
simx --tcut T keeps the row's slow arcs slow for input changes before T and fast (their F delay) after (FIFO across
the cut). T = 0 is the all-fast reference, T = inf the witness. Bisection on T finds T* with run(T*) failing and
run(T* - 1) passing: the two runs are the same up to T*, and differ only in the slowed transitions whose input change
lies in [T* - 1, T*) or that reach the FIFO floor (cut + slow): a 1-ps difference. Their first diverging storage LUT is where the race is decided. Prints T*, those transitions,
the first diverging nodes, and the pin arrivals at the deciding storage LUT in both runs.
(Assumes failure is monotone in T near T*; a non-monotone row gives SOME transition point, flagged if run(T*-1) fails.)
"""
import argparse, json, os, re, subprocess, sys
ap = argparse.ArgumentParser(); ap.add_argument("out"); ap.add_argument("node"); ap.add_argument("pin", type=int); ap.add_argument("kappa")
ap.add_argument("--w", type=int, default=0); ap.add_argument("--routed", default=None); ap.add_argument("--simx", default=None)
a = ap.parse_args(); O = os.path.abspath(a.out)
net = json.load(open(os.path.join(O, "net.json"))); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
ENV = set(idx[x] for x in json.load(open(os.path.join(O, "bnd.json")))["env"])
drv = {g["out"]: gi for gi, g in enumerate(G) if g["out"] not in ENV}
def is_copy(g): return g["k"] == 1 and g["init"] == 2
S = None
for l in open(os.path.join(O, "margins.txt")):
    f = l.split()
    if len(f) > 4 and not l.startswith("#") and f[1] == a.node and f[2] == str(a.pin):
        s_ = [[x.rsplit("/", 1)[0], int(x.rsplit("/", 1)[1])] for x in f[-1].split(",")]
        if f[0] == "w=%d" % a.w: S = s_; break
        if S is None: S = s_
if S is None: sys.exit("row not found")
base = [l for l in open(os.path.join(O, "witness", "command.txt")) if not l.startswith("#")][0].split()
env = {}
while "=" in base[0] and not base[0].startswith("/"): k, v = base.pop(0).split("=", 1); env[k] = v
if a.simx: base[0] = a.simx
def setopt(cmd, opt, val):
    cmd = list(cmd)
    if opt in cmd: cmd[cmd.index(opt) + 1] = val
    else: cmd += [opt, val]
    return cmd
cf = os.path.join(O, "tmp", "tcut_%s_%d.json" % (a.node, a.pin)); os.makedirs(os.path.dirname(cf), exist_ok=True)
json.dump({"S": S, "F": []}, open(cf, "w"))
nsim = 0
def run(T, dump=None):
    global nsim; nsim += 1
    cmd = setopt(setopt(base, "--kappa", a.kappa), "--classes", cf)
    if "--w" in cmd: i = cmd.index("--w"); del cmd[i:i + 2]
    if a.w: cmd += ["--w", str(a.w)]
    cmd = [x for x in cmd if x not in ("--periodic",)] + ["--periodic"]
    if T is not None: cmd += ["--tcut", str(T)]
    if dump: cmd = setopt(cmd, "--tmax", str(T + 20000)) + ["--dump", dump]   # the decision is near T: stop soon after (a capped run writes no dump)
    r = subprocess.run(cmd, capture_output=True, text=True, env=dict(os.environ, **env), cwd=O)
    res = ([x for x in r.stdout.splitlines() if x.startswith("RESULT")] or ["NO-VERDICT"])[0]
    if "unsupported option --tcut" in r.stderr: sys.exit("simx too old: rebuild from simx.cpp")
    return not res.startswith("RESULT OK"), res
f_inf, r_inf = run(None)
f0, r0 = run(0)
print("witness (no cut): %s\nreference (cut at 0, all fast): %s" % (r_inf, r0))
if not f_inf: sys.exit("the row does not fail at kappa %s w %d" % (a.kappa, a.w))
if f0: sys.exit("cut at 0 fails: not the all-fast reference?")
lo, hi = 0, int(env.get("TMAX", "25000000"))
fh, _ = run(hi)
if not fh: hi = 1 << 34
while hi - lo > 1:
    m = (lo + hi) // 2
    if run(m)[0]: hi = m
    else: lo = m
T = hi
fw, rw = run(T, os.path.join(O, "tmp", "tcut_w.json")); fr, rr = run(T - 1, os.path.join(O, "tmp", "tcut_r.json"))
print("T* = %d ps (%d simulations): the full run cut at T* fails, cut at T*-1 passes (dumps below end at T*+20 ns)" % (T, nsim))
W_ = json.load(open(os.path.join(O, "tmp", "tcut_w.json")))["nodes"]; R_ = json.load(open(os.path.join(O, "tmp", "tcut_r.json")))["nodes"]
W_ = {int(k): (bool(v[0]), v[1]) for k, v in W_.items()}; R_ = {int(k): (bool(v[0]), v[1]) for k, v in R_.items()}
names = {}
if os.path.exists(os.path.join(O, "names.txt")):
    for l in open(os.path.join(O, "names.txt")):
        f = l.split()
        if len(f) >= 2: names[f[0]] = f[1].replace("bridge_i.udut.", "")
if a.routed:
    Rj = json.load(open(a.routed))["modules"]["top"]["cells"]
    bel = {c["attributes"].get("NEXTPNR_BEL"): nm for nm, c in Rj.items() if c.get("attributes", {}).get("NEXTPNR_BEL")}
    for n in N:
        m = re.match(r"(SLICE_X\d+Y\d+)\.([A-D])([56])$", n)
        if m: names[n] = bel.get("%s/%s%sLUT" % m.groups(), "").replace("bridge_i.udut.", "")
def nm(n): return N[n] + (" [%s]" % names[N[n]] if names.get(N[n]) else "")
def flips(D, n): return D.get(n, (False, []))[1]
def val(D, n, t):
    v, h = D.get(n, (False, [])); import bisect
    return v ^ (bisect.bisect_right(h, t) & 1)
# run(T*) and run(T*-1) differ only by 1 ps in the slowed transitions in flight at the cut (those with input change at
# T*-1, or arriving at the FIFO floor cut + slow): a 1-ps difference decides the run, so the race there has ~0 slack
def firstdiff(n):
    fw_, fr_ = flips(W_, n), flips(R_, n)
    if W_.get(n, (False,))[0] != R_.get(n, (False,))[0]: return 0
    for x, y in zip(fw_, fr_):
        if x != y: return min(x, y)
    if len(fw_) != len(fr_): return fw_[len(fr_)] if len(fw_) > len(fr_) else fr_[len(fw_)]
    return None
storage = set()
for gi, g in enumerate(G):
    if is_copy(g) or g["out"] in ENV or g["k"] < 2: continue
    srcs = []
    for u in g["ins"]:
        while u in drv and is_copy(G[drv[u]]): u = G[drv[u]]["ins"][0]
        srcs.append(u)
    if g["out"] in srcs: storage.add(gi)
allc = sorted((t, gi) for gi, g in enumerate(G) if g["out"] not in ENV for t in [firstdiff(g["out"])] if t is not None)
def pulses(D, n, t, wmax=20):
    h = [x for x in flips(D, n) if t - 1 <= x <= t + 3000]
    return [(h[i], h[i + 1] - h[i]) for i in range(len(h) - 1) if h[i + 1] - h[i] < wmax]
for t, gi in allc[:12]:
    pw = pulses(W_, G[gi]["out"], t)
    if pw and G[gi]["kind"] in ("lut6", "lut5"):
        print("RUNT: %s pulses %s ps wide at %d ps in the failing run: narrower than H_RUNT's w = 20 (a w = 20 run filters it)"
              % (nm(G[gi]["out"]), "/".join(str(x[1]) for x in pw[:3]), pw[0][0])); break
print("first nodes to diverge: " + ", ".join("%s(%s)@%d" % (nm(G[gi]["out"]), G[gi]["kind"], t) for t, gi in allc[:8]))
st = [(t, gi) for t, gi in allc if gi in storage]
for t, gi in st[:6]: print("  storage diverges: %s at %d ps" % (nm(G[gi]["out"]), t))
if not st: sys.exit("no storage LUT diverges")
t0, q = st[0]; g = G[q]
print("\nDECIDED AT: %s (%s), first differs at %d ps (cut at T* vs T*-1)" % (nm(g["out"]), g["kind"], t0))
for p, u in enumerate(g["ins"]):
    s = u
    while s in drv and is_copy(G[drv[s]]): s = G[drv[s]]["ins"][0]
    def near(D): return [x for x in flips(D, u) if t0 - 3000 <= x <= t0 + 500]
    print("  pin %d <- %-40s  input flips near: cut T* %s | cut T*-1 %s%s" % (p, nm(s), near(W_), near(R_), "  (own output)" if s == g["out"] else ""))
