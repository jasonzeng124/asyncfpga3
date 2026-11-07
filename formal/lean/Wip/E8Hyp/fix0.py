"""UNTRUSTED evidence for the joint-witness precondition of design_verdict8 on gcd_hw:
a time-0 fixpoint (core_hyps_exist's hfix) of the xaudit control skeleton with rst = 1,
constant 0/1 wires, every other primary input X (free). Kleene iteration from all-X
(monotone): if it ends with every LUT output definite, that state is a binary fixpoint
for EVERY choice of the free inputs (Kleene soundness), so hfix holds there.
Routes are identity buffers in the Lean Design, so they do not change the fixpoint."""
import json, sys
X = 2
def keval(init, k, vals):
    # Kleene LUT: definite iff all completions agree
    outs = set()
    xs = [i for i, v in enumerate(vals) if v == X]
    base = sum((v << i) for i, v in enumerate(vals) if v != X)
    for m in range(1 << len(xs)):
        a = base
        for j, i in enumerate(xs):
            if (m >> j) & 1: a |= 1 << i
        outs.add((init >> a) & 1)
        if len(outs) == 2: return X
    return outs.pop()
d = json.load(open(sys.argv[1]))
(top, m), = [(k, v) for k, v in d["modules"].items() if v.get("cells")][:1] if len(d["modules"]) == 1 else [(k, v) for k, v in d["modules"].items() if k == "gcd_ctl"]
cells = {}
for cn, c in m["cells"].items():
    k = int(c["type"][3]); cells[cn] = (k, [c["connections"][f"I{i}"][0] for i in range(k)], c["connections"]["O"][0], int(c["parameters"]["INIT"], 2))
rst = m["ports"]["rig_rst"]["bits"][0]
inputs = [p["bits"][0] for n, p in m["ports"].items() if p["direction"] == "input"]
val = {}
def rd(b):
    if b == "0": return 0
    if b == "1": return 1
    if b == rst: return X if "--norst" in sys.argv else 1
    return val.get(b, X)
it = 0
while True:
    it += 1; ch = 0
    for cn, (k, ins, out, init) in cells.items():
        v = keval(init, k, [rd(b) for b in ins])
        if val.get(out, X) != v:
            assert val.get(out, X) == X, ("non-monotone", cn)
            val[out] = v; ch += 1
    if not ch: break
und = [cn for cn, c in cells.items() if val.get(c[2], X) == X]
free = [b for b in inputs if b != rst]
print(f"module {top}: {len(cells)} LUTs, {len(free)} free inputs (X), rst bit {rst}; {it} sweeps")
print(f"LUT outputs definite at the fixpoint: {len(cells)-len(und)}/{len(cells)}")
for cn in und[:40]: print("  X:", cn)
# binary fixpoint check with free inputs = 0 and X-outputs (if any) = 0
ones = sum(1 for c in cells.values() if val.get(c[2]) == 1)
print(f"outputs at 1: {ones}")
for cn, c in sorted(cells.items()):
    if val.get(c[2]) == 1: print("  1:", cn)
