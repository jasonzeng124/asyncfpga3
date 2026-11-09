# T50: in behaviours of THE circuit (the counterexample dumps the audit has own-checked as GateOKRunt behaviours), does every
# member w of C's reset island hold valR w during reset? reset_quiet_PS gives it on [A + 15 M, R - 1]; with R = 400 ns and
# A + 15 M a few tens of ns, the times below are inside. Absent dump nodes are constants, solved as in runt_check_own.py.
# usage: risl_vs_dumps.py NET.json BND.json RISL_DUMP DUMP.json...
import json, sys, bisect
net = json.load(open(sys.argv[1])); env = set(); bnd = json.load(open(sys.argv[2]))
nodes = net["nodes"]; idx = {n: i for i, n in enumerate(nodes)}; gates = net["gates"]
env = set(idx[n] for n in bnd["env"]); drv = {g["out"]: gi for gi, g in enumerate(gates)}
mem = [tuple(map(int, l.replace('true', '1').replace('false', '0').split())) for l in open(sys.argv[3])]
RST = 186905
for dp in sys.argv[4:]:
    d = json.load(open(dp)); D = {int(k): (v[0], v[1]) for k, v in d["nodes"].items()}
    absent = [n for n in range(len(nodes)) if n not in D]
    for n in absent: D[n] = (False, [])
    for it in range(50):
        ch = 0
        for n in absent:
            if n not in drv or n in env: continue
            g = gates[drv[n]]; a = sum((1 << p) for p, i in enumerate(g["ins"]) if D[i][0] ^ (len(D[i][1]) % 2 == 1))
            v = bool((g["init"] >> a) & 1)
            if v != D[n][0]: D[n] = (v, []); ch += 1
        if ch == 0: break
    val = lambda n, t: D[n][0] ^ (bisect.bisect_right(D[n][1], t) % 2 == 1)
    rst_fl = D[RST][1]
    print(dp.split('/')[-1], "rst v0", D[RST][0], "first rst flip", rst_fl[:1])
    for t in (100000, 200000, 300000, 399999):
        bad = [(w, v, int(val(w, t))) for (w, v, r) in mem if int(val(w, t)) != v]
        print("  t", t, "members", len(mem), "disagreeing with valR:", len(bad), bad[:4])
