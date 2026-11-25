#!/usr/bin/env python3
"""Shard B (UNTRUSTED): interpolate between the baseline and adversarial assignment B at one arbiter
(private path of r1 toward the slow end, of r2 toward the fast end, by λ), bisect λ for the sign change
of (r2 rise - r1 rise) at ustate's pins, and report q's behaviour near the crossing.
usage: tie.py NET.json ARBS.json BND.json PAIR ARBINDEX"""
import json, sys, os
sys.argv = sys.argv[:5] + ["0.5", "0.0"] + sys.argv[5:]
K = int(sys.argv[7])
sys.argv = sys.argv[:7]
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import importlib.util
spec = importlib.util.spec_from_file_location("advlib", os.path.join(HERE, "adv.py"))
src = open(os.path.join(HERE, "adv.py")).read()
src = src[:src.index('base, res0 = run({}, "base")')]          # definitions only
ns = {"__file__": os.path.join(HERE, "adv.py")}
exec(compile(src, "adv.py", "exec"), ns)
run, roles, events, crit, rises, A, g, names = (ns[k] for k in ("run", "roles", "events", "crit", "rises", "A", "g", "names"))
base, res0 = run({}, "tbase")
R = roles(A[K])
ev = events(base, R); t1, t2 = min(ev, key=lambda e: abs(e[0] - e[1]))
P1 = crit(base, R["r1"], t1, 20000); P2 = crit(base, R["r2"], t2, 20000)
s1 = set(n for n, _ in P1); s2 = set(n for n, _ in P2)
p1 = [n for n in s1 - s2 if n < len(g)]; p2 = [n for n in s2 - s1 if n < len(g)]
def at(lam, tag):
    pm = {gi: 0.5 + 0.5 * lam for gi in p1}; pm.update({gi: 0.5 - 0.5 * lam for gi in p2})
    D, res = run(pm, tag)
    r1 = [t for t in rises(D, R["r1"]) if t > 20000]; r2 = [t for t in rises(D, R["r2"]) if t > 20000]
    return D, res, (r1[0] if r1 else None), (r2[0] if r2 else None)
lo, hi = 0.0, 1.0
_, rlo, a1, a2 = at(lo, "t0"); _, rhi, b1, b2 = at(hi, "t1")
print("λ=0: r1", a1, "r2", a2, rlo, "| λ=1: r1", b1, "r2", b2, rhi, flush=True)
for it in range(14):
    mid = (lo + hi) / 2
    D, res, m1, m2 = at(mid, "tm")
    print("λ=%.5f r1 %s r2 %s gap %s %s" % (mid, m1, m2, (m2 - m1) if m1 and m2 else None, res), flush=True)
    if m1 is None or m2 is None: break
    if (m2 - m1) * (a2 - a1) > 0: lo = mid; a1, a2 = m1, m2
    else: hi = mid
    if abs(m2 - m1) < 50: break
qn = R["q"]
v0, ts = D.get(str(qn), [False, []])
near = [t for t in ts if abs(t - min(m1, m2)) < 20000]
print("q (%s) flips near the tie:" % names[qn], near[:40], "total q flips", len(ts))
for nm, n in (("r1", R["r1"]), ("r2", R["r2"]), ("a0", R["a0"])):
    print(" ", nm, [t for t in D.get(str(n), [False, []])[1] if abs(t - min(m1, m2)) < 200000][:12])
