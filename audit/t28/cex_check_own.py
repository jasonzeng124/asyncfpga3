# T28: own check of shard C's counterexample candidate k84b (FOR-RESEARCH C2): is the dumped behaviour a transport
# behaviour of the Lean netlist with every read delay inside Spec.Adm at g = 1, kappa = 0.84 (one corner c = 0)?
# Delays: the stated adversary -- every pin arc of a gate whose output is in SLOW at floor(1.84 fmax), every other arc
# at ceil(0.16 fmin); SLOW = the named node plus the copy chains (k = 1, INIT = 2) feeding its driver's pins.
# For every gate with all its nodes in the dump: at every time T >= its start (and >= every pin delay), at every candidate
# change time (input flip + pin delay, own output flips), out(T) == INIT[addr(in_i(T - d_i))].  Also checks every delay
# against Adm at c = 0 exactly (rationals) and reports the outputs.  usage: cex_check_own.py NET.json DUMP.json NODE BND.json
import json, sys, bisect, math
from fractions import Fraction as F
net = json.load(open(sys.argv[1])); dump = json.load(open(sys.argv[2])); slow_name = sys.argv[3]
K = F(84, 100); g = F(1)
nodes = net["nodes"]; idx = {n: i for i, n in enumerate(nodes)}; gates = net["gates"]
drv = {gt["out"]: gi for gi, gt in enumerate(gates)}
SLOW = {idx[slow_name]}
for n0 in list(SLOW):
    for u in gates[drv[n0]]["ins"]:
        while u in drv and gates[drv[u]]["k"] == 1 and gates[drv[u]]["init"] == 2:
            SLOW.add(u); u = gates[drv[u]]["ins"][0]
D = {int(k): (v[0], v[1]) for k, v in dump["nodes"].items()}
ENV = set(idx[n] for n in json.load(open(sys.argv[4]))["env"]) if len(sys.argv) > 4 else set()
# nodes absent from the dump are taken as CONSTANT; their value is solved from their driver (fixed point at a late
# time), then every gate -- including those -- is checked over the whole run like the others.
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
bad_adm = 0; checked = 0; skipped = 0; mism = []
for gi, gt in enumerate(gates):
    ds = []
    for e in gt["arcs"]:
        d = math.floor(e["fmax"] * (1 + 0.84)) if gt["out"] in SLOW else math.ceil(e["fmin"] * (1 - 0.84))   # the adversary's own float rounding (e.g. ceil(225 * 0.16) = 37 in binary floating point); Adm is checked exactly below
        lo = (1 - K) * e["fmin"] / g; hi = (1 + K) * e["fmax"] * g
        if not (lo <= d <= hi): bad_adm += 1
        ds.append(d)
    if gt["out"] in ENV: skipped += 1; continue      # env-driven boundary node: its driver is cut in `circuit`
    checked += 1
    start = max([math.ceil((1 + K) * e["smax"] * g) for e in gt["arcs"]] + ds + [0])
    cand = set(t for t in D[gt["out"]][1] if t >= start)
    for i, d in zip(gt["ins"], ds):
        cand.update(t + d for t in D[i][1] if t + d >= start)
    cand.add(start)
    for T in cand:
        a = sum((1 << p) for p, (i, d) in enumerate(zip(gt["ins"], ds)) if val(i, T - d))
        want = bool((gt["init"] >> a) & 1)
        if val(gt["out"], T) != want: mism.append((gt["name"], T)); break
print("slow nodes", len(SLOW), "gates checked", checked, "skipped (env-driven output)", skipped, "delays outside Adm(c=0)", bad_adm)
print("gates whose dumped output disagrees with transport at the adversary's delays:", len(mism), mism[:5])
print("outs", dump["outs"], "pairs", dump["pairs"], "tend", dump["tend"])
