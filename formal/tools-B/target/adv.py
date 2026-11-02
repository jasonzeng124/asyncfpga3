#!/usr/bin/env python3
"""Shard B (UNTRUSTED): can the two requests of a target arbiter be made to arrive together
under the SEQUENTIAL env with in-band delays (Spec Adm at g = 1, κ = 0, one corner)?
For each arbiter: pin roles from the decoded ustate INIT; baseline run (all arcs mid-window);
'both requests rise from idle' events at ustate's pins; then two adversarial runs that put the
private backward cone of one request pin at the window's slow end and the other's at its fast
end. If the arrival order flips, an intermediate in-band assignment makes them coincide.
usage: adv.py NET.json ARBS.json BND.json PAIR [corner] [kappa]"""
import json, subprocess, sys, os
from collections import defaultdict
from bisect import bisect_right
HERE = os.path.dirname(os.path.abspath(__file__))
NETF, ARBF, BNDF, PAIR = sys.argv[1:5]
CORNER = sys.argv[5] if len(sys.argv) > 5 else "0.5"
KAPPA = sys.argv[6] if len(sys.argv) > 6 else "0.0"
TMP = os.environ.get("TMPDIR", "/tmp")
N = json.load(open(NETF)); A = json.load(open(ARBF)); B = json.load(open(BNDF))
g = N["gates"]; names = N["nodes"]; idx = {n: i for i, n in enumerate(names)}
ENV = set(idx[x] for x in B["env"])

def F(init, v):  # v: list of 6 bits
    a = sum(b << i for i, b in enumerate(v)); return (init >> a) & 1

def roles(a):
    q = a["qi"]; G = g[q]; ins = G["ins"]
    def src(n):
        h = 0
        while n < len(g) and g[n]["k"] == 1 and h < 500: n = g[n]["ins"][0]; h += 1
        return n
    fb = [i for i, n in enumerate(ins) if src(n) == q]
    rst = [i for i, n in enumerate(ins) if src(n) == idx[B["boundary"]["rst"]]]
    vcc = [i for i, n in enumerate(ins) if "VCC" in names[src(n)]]
    rest = [i for i in range(G["k"]) if i not in fb + rst + vcc]
    assert len(fb) == 1 and len(rst) == 1 and len(rest) == 3, (G["name"], fb, rst, vcc, rest)
    fb, rst = fb[0], rst[0]
    def val(assign):
        v = [0] * G["k"]
        for i in vcc: v[i] = 1
        for i, b in assign.items(): v[i] = b
        return F(G["init"], v)
    a0 = [p for p in rest if all(val({p: 1, fb: f, rst: 0, **{o: x for o, x in zip([r for r in rest if r != p], xs)}}) == f
                                  for f in (0, 1) for xs in ((0, 0), (0, 1), (1, 0), (1, 1)))]
    assert len(a0) == 1, (G["name"], a0)
    a0 = a0[0]; rr = [p for p in rest if p != a0]
    # r1 = set pin: alone high (A0 = 0) gives 1 whatever fb
    r1 = [p for p in rr if all(val({p: 1, [x for x in rr if x != p][0]: 0, a0: 0, rst: 0, fb: f}) == 1 for f in (0, 1))]
    assert len(r1) == 1, (G["name"], r1)
    r1 = r1[0]; r2 = [p for p in rr if p != r1][0]
    return dict(q=q, r1=ins[r1], r2=ins[r2], a0=ins[a0], rst=ins[rst], fb=ins[fb])

def cone(n0):
    seen, todo, gs = {n0}, [n0], set()
    while todo:
        n = todo.pop()
        if n in ENV or n >= len(g): continue
        gs.add(n)
        for i in g[n]["ins"]:
            if i not in seen: seen.add(i); todo.append(i)
    return gs

def run(posmap, tag):
    pm = os.path.join(TMP, "pm_%s.json" % tag); dp = os.path.join(TMP, "dump_%s.json" % tag)
    json.dump({str(k): v for k, v in posmap.items()}, open(pm, "w"))
    out = subprocess.run([sys.executable, "-I", os.path.join(HERE, "simb.py"), NETF, BNDF, "--pairs", PAIR,
                          "--corner", CORNER, "--kappa", KAPPA, "--tmax", "200000000", "--posmap", pm, "--dump", dp],
                         capture_output=True, text=True)
    res = [l for l in out.stdout.splitlines() if "RESULT" in l]
    return json.load(open(dp))["nodes"], (res[0] if res else out.stdout[-300:] + out.stderr[-300:])

def rises(D, n):
    v0, ts = D.get(str(n), [False, []]); v = v0; r = []
    for t in ts:
        v = not v
        if v: r.append(t)
    return r

def val_at(D, n, t):
    v0, ts = D.get(str(n), [False, []]); return v0 ^ (sum(1 for x in ts if x <= t) % 2 == 1)

def events(D, R):
    ev = []
    for t1 in rises(D, R["r1"]):
        for t2 in rises(D, R["r2"]):
            tf = min(t1, t2)
            other = R["r2"] if t1 <= t2 else R["r1"]
            if not val_at(D, other, tf - 1) and abs(t1 - t2) < 2_000_000:
                ev.append((t1, t2))
    return ev

def dmid(e):
    c = float(CORNER)
    lo = (1 - c) * e["fmin"] + c * e["smin"]; hi = (1 - c) * e["fmax"] + c * e["smax"]
    return int(round(lo + 0.5 * (hi - lo)))

def crit(D, n, t, R0):
    """Backtrace the event 'node n flips at t' to its cause, gate by gate."""
    path = []
    while True:
        path.append((n, t))
        if n in ENV or n >= len(g) or t <= R0: return path
        G = g[n]; best = None
        for i, m in enumerate(G["ins"]):
            tr = t - dmid(G["arcs"][i])
            ts = D.get(str(m), [False, []])[1]
            k = bisect_right(ts, tr)
            if k:
                lf = ts[k - 1]
                if best is None or lf > best[1]: best = (m, lf)
        if best is None: return path
        n, t = best

base, res0 = run({}, "base")
print("baseline", PAIR, "corner", CORNER, res0)
for k, a in enumerate(A):
    R = roles(a)
    ev = events(base, R)
    if not ev:
        print("arb %d %s: no both-from-idle event" % (k, g[R["q"]]["name"])); continue
    t1, t2 = min(ev, key=lambda e: abs(e[0] - e[1]))
    R0 = 20000
    P1 = crit(base, R["r1"], t1, R0); P2 = crit(base, R["r2"], t2, R0)
    s1 = set(n for n, _ in P1); s2 = set(n for n, _ in P2)
    causal = any(n in s1 and tt == t1 for n, tt in P2)   # r2's cause chain passes r1's own rise
    common = [x for x in P1 if x in set(P2)]
    p1 = set(n for n in s1 - s2 if n < len(g)); p2 = set(n for n in s2 - s1 if n < len(g))
    print("   arb %d paths: r1 %d hops back to %s@%d, r2 %d hops back to %s@%d, first common event %s, r2 depends on r1: %s" % (
        k, len(P1), names[P1[-1][0]][:30], P1[-1][1], len(P2), names[P2[-1][0]][:30], P2[-1][1],
        (names[common[0][0]][:30], common[0][1]) if common else None, causal))
    out = []
    for tag, sa, sb in (("A", 2, -1), ("B", -1, 2)):
        pm = {gi: sa for gi in p1}; pm.update({gi: sb for gi in p2})
        D, res = run(pm, "%d%s" % (k, tag))
        e2 = events(D, R)
        best = min(e2, key=lambda e: abs(e[0] - e[1])) if e2 else None
        out.append((tag, best, best and best[1] - best[0], res.split(":")[0]))
    print("arb %d %s: base r1@%d r2@%d (r2-r1 = %d); private cones %d/%d gates;" % (
        k, g[R["q"]]["name"], t1, t2, t2 - t1, len(p1), len(p2)), out, flush=True)
