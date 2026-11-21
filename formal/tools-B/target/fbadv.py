#!/usr/bin/env python3
"""Shard B (UNTRUSTED): adversarial test of one storage node's fb_switch margin. Node GATE (a feedback
LUT) flips at time T0 in the baseline dump and its forcing episode ends when pin P's node changes at
TEND. Put the causal path of that pin change (back to GATE's own output flip) at the fast end of its
windows and GATE's feedback route + GATE itself at the slow end, rerun, rescan.
usage: fbadv.py NET.json ARBS.json BND.json PAIR GATENAME T0 KAPPA"""
import json, sys, os, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
NETF, ARBF, BNDF, PAIR, GNAME, T0, KAPPA = sys.argv[1:8]; T0 = int(T0)
TMP = os.environ.get("TMPDIR", "/tmp")
src = open(os.path.join(HERE, "adv.py")).read(); src = src[:src.index('base, res0 = run({}, "base")')]
sys.argv = [sys.argv[0], NETF, ARBF, BNDF, PAIR, "0.5", KAPPA]
ns = {"__file__": os.path.join(HERE, "adv.py")}; exec(compile(src, "adv.py", "exec"), ns)
g, crit, run = ns["g"], ns["crit"], ns["run"]
gi = [i for i, G in enumerate(g) if G["name"] == GNAME][0]; G = g[gi]
base, r0 = run({}, "fb0")
# feedback pin and route
fbj, route = None, []
for j, n in enumerate(G["ins"]):
    m, ch = n, []
    while m < len(g) and g[m]["k"] == 1 and m != gi and len(ch) < 60: ch.append(m); m = g[m]["ins"][0]
    if m == gi: fbj, route = j, ch; break
# the episode end: the first non-feedback pin node flip after T0 that ends the forcing (take all pin flips in (T0, T0+5000))
cands = []
for j, n in enumerate(G["ins"]):
    if j == fbj: continue
    for t in base.get(str(n), [False, []])[1]:
        if T0 - 2000 < t < T0 + 5000: cands.append((t, j, n))
print("baseline", r0, "| gate", GNAME, "fb pin", fbj, "route hops", len(route), "| pin flips near T0:", cands)
fast = set()
for t, j, n in cands:
    if t > T0 - 500:
        P = crit(base, n, t, T0 - 1)       # back-trace this pin change to before T0
        fast |= set(m for m, _ in P if m < len(g) and m != gi and m not in route)
slow = set(route) | {gi}
pm = {m: -1 for m in fast}; pm.update({m: 2 for m in slow})
D, r1 = run(pm, "fb1")
print("adversarial (κ=%s): %d gates fast, %d slow ->" % (KAPPA, len(fast), len(slow)), r1)
dump = os.path.join(TMP, "dump_fb1.json")
out = subprocess.run([sys.executable, "-I", os.path.join(HERE, "fbscan.py"), NETF, dump], capture_output=True, text=True).stdout
print("\n".join(l for l in out.splitlines() if GNAME in l or "shorter" in l or "feedback gates" in l))
