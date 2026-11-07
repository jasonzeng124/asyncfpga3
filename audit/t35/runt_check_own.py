# T35: own check of shard A's candidate counterexample under H_RUNT(w) (formal f446facf, FOR-RESEARCH A4).
# Is the dumped behaviour a GateOKRunt w behaviour (SpecRunt.lean: H_RUNT on LUT pins only, lutGate = name ends LUT.O6/.O5)
# of the Lean netlist at g = 1, kappa = KN/KD, corner c = 0?  Own witness read maps, built independently of formal's tools:
#   non-LUT pin i: f_i(t) = t - d_i (transport);
#   LUT pin i:     f_i(t) = greatest u <= t - d_i lying in no pulse (maximal constant interval [a,b), b-a < w; [0, first flip)
#                  counts, Pulse's a = 0 case) -- monotone and <= t by construction;
#   d_i = the stated adversary: floor((1+k) fmax) if the gate's output is in SLOW (named nodes + the copy chains feeding
#   their drivers' pins), else ceil((1-k) fmin); LUT pins raised to >= w.
# Checks, exactly in rationals: every d_i inside Adm(c=0); every lag t - f_i(t) <= (1+k) fmax for every t >= start (worst
# lag = d + length of the narrow-pulse chain skipped); no read in a narrow [0, first flip); output == INIT[addr] at every
# candidate change time.  usage: runt_check_own.py NET.json DUMP.json BND.json W KN KD SLOWNODE...  (gates driving BND env nodes are cut, as `circuit` does)
import json, sys, bisect, math
from fractions import Fraction as F
net = json.load(open(sys.argv[1])); dump = json.load(open(sys.argv[2])); ENV = set(); W = int(sys.argv[4])
K = F(int(sys.argv[5]), int(sys.argv[6])); slow_names = sys.argv[7:]
SLOWARC = None; FLOAT = False
import os; G = F(os.environ.get('AUDIT_G', '1')); SSLACK = int(os.environ.get('AUDIT_SSLACK', '0')); SSLUT = os.environ.get('AUDIT_SSLACK_LUT', '0') == '1'   # T39: slow arcs at floor((1+k) fmax g) - SSLACK (only on LUT pins if SSLUT)
EX = dict(tuple(map(int, x.split(':'))) for x in os.environ.get('AUDIT_EX', '').split(',') if x)   # T39: explicit per-arc delays, code 8*out+pin -> d (still checked against Adm)   # guard g (T38); Adm = [(1-k) fmin / g, (1+k) fmax g], start uses (1+k) smax g
if slow_names and slow_names[0].endswith('.json'):   # per-arc classes {S: [[out node, pin], ...]} (C's convention); rest fast
    SLOWARC = set((n, p) for n, p in json.load(open(slow_names[0]))['S']); FLOAT = 'float' in slow_names[1:]; slow_names = []
nodes = net["nodes"]; idx = {n: i for i, n in enumerate(nodes)}; gates = net["gates"]
drv = {gt["out"]: gi for gi, gt in enumerate(gates)}
ENV = set(idx[n] for n in json.load(open(sys.argv[3]))["env"])
SLOW = set(idx[s] for s in slow_names)
for n0 in list(SLOW):
    for u in gates[drv[n0]]["ins"]:
        while u in drv and gates[drv[u]]["k"] == 1 and gates[drv[u]]["init"] == 2:
            SLOW.add(u); u = gates[drv[u]]["ins"][0]
D = {int(k): (v[0], v[1]) for k, v in dump["nodes"].items()}
absent = [n for n in range(len(nodes)) if n not in D]
for n in absent: D[n] = (False, [])
for it in range(50):
    ch = 0
    for n in absent:
        if n not in drv or n in ENV: continue
        gt = gates[drv[n]]
        a = sum((1 << p) for p, i in enumerate(gt["ins"]) if D[i][0] ^ (len(D[i][1]) % 2 == 1))
        v = bool((gt["init"] >> a) & 1)
        if v != D[n][0]: D[n] = (v, []); ch += 1
    if ch == 0: break
print("absent nodes taken constant:", len(absent), "fixed point after", it, "rounds")
def val(n, t):
    v0, fl = D[n]; return v0 ^ (bisect.bisect_right(fl, t) % 2 == 1)
def lut(gt): return gt["name"].endswith("LUT.O6") or gt["name"].endswith("LUT.O5")
NARROW = {}
def narrow(n):   # list of (a, b, a_chain): maximal intervals [a,b) narrower than W, with the start of the narrow chain ending at b
    if n in NARROW: return NARROW[n]
    fl = D[n][1]; bounds = [0] + fl; out = []; chain = None
    for k in range(len(fl)):
        a, b = bounds[k], fl[k]
        if b - a < W:
            chain = a if chain is None else chain; out.append((a, b, chain))
        else: chain = None
    NARROW[n] = out; return out
def f_read(n, u):  # greatest v <= u not in a narrow interval of n; None if none >= 0
    nr = narrow(n)
    k = bisect.bisect_right([a for a, b, c in nr], u) - 1
    if k >= 0 and nr[k][0] <= u < nr[k][1]:
        c = nr[k][2]; return None if c == 0 else c - 1
    return u
bad_adm = 0; bad_lag = 0; pow_reads = 0; checked = 0; mism = []; luts = 0; raised = 0; maxlag_ratio = F(0)
for gi, gt in enumerate(gates):
    if gt["out"] in ENV: continue      # env-driven boundary node: its driver is cut in `circuit`
    ds = []; L = lut(gt); luts += L
    for e in gt["arcs"]:
        sl = (nodes[gt["out"]], len(ds)) in SLOWARC if SLOWARC is not None else gt["out"] in SLOW
        if FLOAT: d = math.floor(e["fmax"] * (1 + float(K))) if sl else math.ceil(e["fmin"] * (1 - float(K)))   # adversary's float rounding; Adm checked exactly
        else: d = math.floor((1 + K) * e["fmax"] * G) - (SSLACK if (not SSLUT or L) else 0) if sl else math.ceil((1 - K) * e["fmin"] / G)
        if 8 * gt["out"] + len(ds) in EX: d = EX[8 * gt["out"] + len(ds)]
        if L and d < W: d = W; raised += 1
        lo = (1 - K) * e["fmin"] / G; hi = (1 + K) * e["fmax"] * G
        if not (lo <= d <= hi): bad_adm += 1
        ds.append(d)
    checked += 1
    start = max([math.ceil((1 + K) * e["smax"] * G) for e in gt["arcs"]] + ds + [0])
    if L:   # lag check over every narrow chain the read window can enter at t >= start
        for i, d, e in zip(gt["ins"], ds, gt["arcs"]):
            hi = (1 + K) * e["fmax"] * G
            for a, b, c in narrow(i):
                if b - 1 + d < start: continue
                if c == 0: pow_reads += 1; continue
                lag = d + (b - 1) - (c - 1)          # worst at t - d = b - 1
                if lag > hi: bad_lag += 1
                if e["fmax"] > 0: maxlag_ratio = max(maxlag_ratio, F(lag) / e["fmax"])
    cand = set(t for t in D[gt["out"]][1] if t >= start)
    for i, d in zip(gt["ins"], ds):
        cand.update(t + d for t in D[i][1] if t + d >= start)
    cand.add(start)
    for T in sorted(cand):
        a = 0
        for p, (i, d) in enumerate(zip(gt["ins"], ds)):
            u = f_read(i, T - d) if L else T - d
            if u is None: u = 0
            if val(i, u): a |= 1 << p
        if val(gt["out"], T) != bool((gt["init"] >> a) & 1): mism.append((gt["name"], T)); break
print("W", W, "kappa", K, "g", G, "slow nodes", len(SLOW), "gates checked", checked, "LUT gates", luts, "LUT pin delays raised to W", raised)
print("delays outside Adm(c=0):", bad_adm, " LUT-pin lag violations:", bad_lag, " reads into a narrow power-up interval:", pow_reads,
      " max lag/fmax on LUT pins:", float(maxlag_ratio))
print("gates whose dumped output disagrees:", len(mism), mism[:8])
print("outs", dump["outs"], "pairs", dump["pairs"], "tend", dump["tend"])
