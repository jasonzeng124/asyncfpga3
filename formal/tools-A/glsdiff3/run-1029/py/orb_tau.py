#!/usr/bin/env python3
"""orb_tau.py -- Float experiment (NOT a proof) on the Lean OR-loop orbit
(Formal.Cells.CElemInvolution.orb, transcribed in ../../../glsdiff/orb_crit.py) with the
symmetric exp involution channel delta(T) = Tp + tau ln(2 - e^{-(T+Tp)/tau}),
delta_inf = TLOOP.  For each tau: the critical runt width s*, and near s* the
resolution time t_r (time of the last surviving transition) and the number of pulses the
loop emits to its fanout before it settles, as a function of the offset e = s - s*.
Fits t_r = TAU_eff * ln(1/|e|) + const, the law FID_RESOLVE uses (t_r = TAU ln(WIN/2|delta|)).
Usage: python3 -I orb_tau.py [TLOOP]"""
import math, sys
def mk(Tp, tau):
    def d(T):
        a = 2 - math.exp(-(T + Tp) / tau)
        return None if a <= 0 else Tp + tau * math.log(a)
    return d, Tp + tau * math.log(2)
def orbit(d, dinf, s, N=200000):
    """returns (outcome, transitions list) ; transitions are output edge times, rise first"""
    o = [dinf]
    x = d(s - dinf)
    if x is None: return 'L', o[:0]
    o.append(s + x)
    if o[1] <= o[0]: return 'L', []
    for n in range(N):
        x = d(o[n] - o[n + 1])
        if x is None: return ('L' if n % 2 == 0 else 'H'), o[:n + 1]
        nxt = o[n] + x
        if nxt <= o[n + 1]:
            return ('H' if n % 2 == 0 else 'L'), o[:n + 1]
        o.append(nxt)
    return 'O', o
def crit(d, dinf):
    lo, hi = 1e-6, dinf - 1e-6
    for _ in range(200):
        m = (lo + hi) / 2
        if orbit(d, dinf, m)[0] == 'H': hi = m
        else: lo = m
        if hi - lo < 1e-11: break
    return lo, hi
TLOOP = float(sys.argv[1]) if len(sys.argv) > 1 else 424.0
print("TLOOP %g ps (delta_inf).  FID_RESOLVE noise-free centre TLOOP-WIN/2 = %g (WIN 150)" % (TLOOP, TLOOP - 75))
print("tau  s*      s*/TLOOP | e(ps): outcome, #edges emitted, t_r(ps) after the runt | TAU_eff fit (ps)  TAU_eff/TLOOP")
for tau in (20, 40, 60, 100, 150, 200):
    Tp = TLOOP - tau * math.log(2)
    d, dinf = mk(Tp, tau)
    lo, hi = crit(d, dinf); sc = (lo + hi) / 2
    pts = []; cells = []
    for e in (-30, -10, -1, -0.1, -0.01, 0.01, 0.1, 1, 10, 30):
        oc, tr = orbit(d, dinf, sc + e)
        t_r = (tr[-1] if tr else 0.0)
        cells.append("%+g:%s,%d,%.0f" % (e, oc, len(tr), t_r))
        if abs(e) <= 1: pts.append((math.log(1 / abs(e)), t_r))
    # least-squares slope of t_r against ln(1/|e|) on |e| <= 1
    n = len(pts); mx = sum(p[0] for p in pts) / n; my = sum(p[1] for p in pts) / n
    sl = sum((p[0] - mx) * (p[1] - my) for p in pts) / sum((p[0] - mx) ** 2 for p in pts)
    print("%3d %7.2f  %.3f | %s | %.0f  %.2f" % (tau, sc, sc / dinf, "  ".join(cells), sl, sl / dinf))
