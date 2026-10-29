"""run_onecorner.py -- probe C-12d: re-run C-12a's arbiter checks with ONE
consistent prjxray corner (rise = fall) and with the corner model (shared
corner c, local scatter kappa), instead of the fast-rise / slow-fall mix.

prjxray SDF triples are (FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX), corners, not
rise/fall (prjxray utils/makesdf.py:63).  C-12a's arb.arcs() used
O6 rise 45..56 / fall 100..124 and O5 rise 44..52 / fall 122..150: a mix.
Here arb.arcs is replaced (monkeypatched, arb.py itself is unchanged) by one
interval per output used for BOTH edges:

  FAST   O6 [45, 56]    O5 [42, 55]     (O5: union over pins I0..I2)
  SLOW   O6 [100, 124]  O5 [121, 152]
  CM(c,k) corner model: nominal D(c) = lerp(FAST_MAX, SLOW_MAX, c),
         arc in [(1-k) D(c), (1+k) D(c)]  (Formal/Core/Delay/Corner.lean Scat)

spread=False (the tb/bd_prims_sim reading: one fixed arc) uses the interval's
max for both edges.  Every inert channel still draws each transition's delay
independently inside the interval, so 'interval' rows allow rise != fall
within one corner's band (a superset of the auditor's rise = fall points).

Sections (results/onecorner_<section>.txt):
  tb        bare arbcell, bd_prims_sim semantics (route lumped into an
            inertial arc), route 0: the header's '16 ps' race
  real      bare arbcell, transport routes 0 / 48 ps, free requests, and the
            aperture (smallest H_SEP) at 48 ps
  arbiter   shipped bd_arbiter, A0->ua2 fork: smallest extra delay giving
            an early ack (C-12a: k >= 10 with rise (2,2) fall (4,5))
Usage: python3.13 run_onecorner.py [section ...]
"""
import os
import sys
import time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arb
import tsmc

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results')
os.makedirs(OUT, exist_ok=True)
LOG = None

# prjxray CLBLL_L.sdf (B-arb-corners.md table), ps: (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX)
PRJ = dict(o6=(45, 56, 100, 124),       # A6LUT A1..A6 -> O6 (flat)
           o5=(42, 55, 121, 152))       # A5LUT -> O5, union over pins I0..I2
FAST = {k: (v[0], v[1]) for k, v in PRJ.items()}
SLOW = {k: (v[2], v[3]) for k, v in PRJ.items()}
K11, KE = 1 / 11, 383 / 1927            # rule A's and rule E's kappa limits (Corner.lean)


def lerp(f, s, c):
    return f + c * (s - f)


def lit(c, k):
    """A's corner model, literal endpoints (B-arb-kappa 'lit'): F = FAST_MIN,
    S = SLOW_MAX; arc in [(1-k) D(c), (1+k) D(c)]."""
    return {n: ((1 - k) * lerp(v[0], v[3], c), (1 + k) * lerp(v[0], v[3], c)) for n, v in PRJ.items()}


def cons(c, k):
    """Corner model on top of prjxray's corner windows (B-arb-kappa 'cons'):
    arc in [(1-k) lerp(FMIN, SMIN, c), (1+k) lerp(FMAX, SMAX, c)].  k = 0, c = 0/1
    are exactly the FAST / SLOW bands."""
    return {n: ((1 - k) * lerp(v[0], v[2], c), (1 + k) * lerp(v[1], v[3], c)) for n, v in PRJ.items()}


def cm(c, k):          # kept for the earlier (unlogged) run: lerp(FAST_MAX, SLOW_MAX)
    d6 = 56 + c * (124 - 56)
    d5 = 55 + c * (152 - 55)
    return dict(o6=((1 - k) * d6, (1 + k) * d6), o5=((1 - k) * d5, (1 + k) * d5))


CORNERS = [('FAST', FAST), ('SLOW', SLOW)]
for _c in (0, 0.5, 1):
    for _kn, _k in (('1/11', K11), ('kE', KE)):
        CORNERS.append(('lit c=%g k=%s' % (_c, _kn), lit(_c, _k)))
        CORNERS.append(('cons c=%g k=%s' % (_c, _kn), cons(_c, _k)))
CUR = FAST


def arcs_onecorner(tick=4, spread=True):
    def iv(lo, hi):
        if not spread:
            lo = hi
        return (arb.ticks(lo, tick, False), arb.ticks(hi, tick, True))
    o6 = iv(*CUR['o6'])
    o5 = iv(*CUR['o5'])
    return (o6, o6), (o5, o5)          # rise == fall interval


arb.arcs = arcs_onecorner


def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    LOG.write(s + '\n')
    LOG.flush()


def wv(ts, tr):
    log('\n'.join('     ' + l for l in tsmc.wave(ts, tr, list(ts.show)).split('\n')))


def kres(r):
    if r[0] == 'cex':
        return 'CEX@%d' % r[1]
    return '%s (k=%d)' % (r[0], r[1])


def sec_tb():
    global CUR
    log('# bare bd_arbcell, bd_prims_sim semantics (route lumped into the inertial arc),')
    log('# route 0, r1/r2 free (level >= P ticks). C-12a (mixed 56/124): CEX at route 0, overlap 16 ps.')
    for name, cor in CORNERS:
        CUR = cor
        for spread in (False, True):
            tick = 4 if cor['o6'][1] < 80 else 8
            mk = lambda: arb.arbcell(tick=tick, spread=spread, route=0,
                                     P=40 if tick == 4 else 20, lumped=True)
            ts, P = mk()
            t = time.time()
            r = tsmc.kind(ts, P['mutex'], 90)
            log('  %-18s %-8s tick=%dps arcs(ticks)=%s mutex: %-16s [%d bits, %.1fs]' % (
                name, 'interval' if spread else 'max', tick, arb.arcs(tick, spread),
                kres(r), ts.nbits(), time.time() - t))
            if r[0] == 'cex':
                wv(ts, r[2])


def sec_real():
    global CUR
    log('# bare bd_arbcell, transport routes on q and on r1/r2 into both LUTs, tick 8 ps,')
    log('# corner intervals (rise = fall band), free requests (P = min level time).')
    log('# C-12a (mixed): mutex CEX at routes 0/48/100; aperture 152 ps at 48 ps.')
    tick = 8
    D = dict(CORNERS)
    names = os.environ.get('REAL_CORNERS', 'FAST,SLOW,cons c=0 k=1/11,cons c=1 k=1/11').split(',')
    for name in names:
        cor = D[name]
        CUR = cor
        for route in (0, 48):
            mk = lambda sep=0, P=50: arb.arbcell(tick=tick, spread=True, route=route,
                                                 rroute=route, P=P, sep=sep)
            ts, P = mk()
            t = time.time()
            d, tr = tsmc.bmc(ts, P['mutex'], 60)
            log('== %s route %d ps: free env mutex: %s [%.1fs]' % (
                name, route, 'CEX@%s' % d if d is not None else 'none to 60', time.time() - t))
            if d is None:
                continue
            wv(ts, tr)
            if route != 48:
                continue
            lo, hi, last = 1, 64, None
            while lo < hi:
                mid = (lo + hi) // 2
                ts, P = mk(sep=mid, P=mid)
                d, tr = tsmc.bmc(ts, P['mutex'], 50)
                if d is None:
                    hi = mid
                else:
                    lo, last = mid + 1, (mid, ts, tr)
            log('   aperture (bounded, depth 50): sep >= %d ticks = %d ps' % (lo, lo * tick))
            ts, P = mk(sep=lo, P=lo)
            t = time.time()
            r = tsmc.kind(ts, P['mutex'], 70)
            log('   k-induction at sep=%d: %s [%.1fs]' % (lo, kres(r), time.time() - t))
            if last:
                log('   counterexample at sep=%d:' % last[0])
                wv(last[1], last[2])


ARB_UNITS = [  # 1 unit = 25 ps, nearest rounding (coarse; dense-time answers are zone/onecorner.py)
    ('FAST', ((2, 2), (2, 2)), ((2, 2), (2, 2))),   # O6 45-56 -> 1.8-2.24; O5 42-55 -> 1.7-2.2
    ('SLOW', ((4, 5), (4, 5)), ((5, 6), (5, 6))),   # O6 100-124 -> 4-4.96; O5 121-152 -> 4.8-6.1
    ('MIX12a', ((2, 2), (4, 5)), ((2, 2), (4, 5))),  # C-12a's rise (2,2) / fall (4,5): the corner mix
]
PROPS = ('mutex', 'ackmutex', 'tx')


def sec_arbiter():
    log('# shipped bd_arbiter, four-phase clients (Lc=1) and server (latency >= Ls), route 1 unit')
    log('# on every net, 1 unit = 25 ps, one interval per output used for BOTH edges (O6: q, g2,')
    log('# A1, A2; O5: R0, g1).  Properties: mutex g1&g2, ackmutex A1&A2, tx (12b: an A_k rise')
    log('# with no A0 rise since the last acknowledge).  BMC depth 60.')
    for name, l6, l5 in ARB_UNITS:
        for Ls in (1, 2, 4):
            ts, P = arb.arbiter(lut=l6, lut5=l5, route=1, Ls=Ls)
            for pr in PROPS:
                t = time.time()
                d, tr = tsmc.bmc(ts, P[pr], 60)
                log('  %-7s Ls=%d fork 0: %-8s %s [%d bits, %.1fs]' % (
                    name, Ls, pr, 'CEX@%s' % d if d is not None else 'none to 60', ts.nbits(), time.time() - t))
                if d is not None:
                    wv(ts, tr)


def sec_fork():
    log('# A0 fork, falling edge (12a 2d / B ArbA0Fork): extra delay k on the A0 branch into ua2;')
    log('# smallest k with an early/extra acknowledge (tx).  Ls = 4 (slow-enough server), BMC 60.')
    for name, l6, l5 in ARB_UNITS:
        def bad(k):
            ts, P = arb.arbiter(lut=l6, lut5=l5, route=1, a0fork=(0, 0, k), Ls=4)
            t = time.time()
            d, tr = tsmc.bmc(ts, P['tx'], 60)
            log('  %-7s A0->ua2 extra %2d: tx %s [%d bits, %.1fs]' % (
                name, k, 'CEX@%s' % d if d is not None else 'none to 60', ts.nbits(), time.time() - t))
            return d is not None, ts, tr
        hi = 24
        b, ts, tr = bad(hi)
        if not b:
            log('  => %s: no early ack up to %d' % (name, hi))
            continue
        lo, best = 0, (hi, ts, tr)
        while lo < hi:
            mid = (lo + hi) // 2
            b, ts, tr = bad(mid)
            if b:
                hi, best = mid, (mid, ts, tr)
            else:
                lo = mid + 1
        log('  => %s: smallest A0->ua2 extra delay with an early ack: %d units' % (name, best[0]))
        wv(best[1], best[2])


def sec_fork2():
    log('# SLOW one corner, deeper BMC (depth 90): sec_fork found no early ack up to 24 extra')
    log('# units at depth 60, too shallow for SLOW (one transaction ~ 30 ticks).  Prediction by')
    log('# the FAST trace: early ack iff 1 + k >= (route + q + route + g2 + route) + ua2 arc, i.e.')
    log('# k >= 3*lut_lo + 2*route = 14 at SLOW (4,5), 8 at FAST (2,2).')
    name, l6, l5 = ARB_UNITS[1]
    for k in (14, 13):
        ts, P = arb.arbiter(lut=l6, lut5=l5, route=1, a0fork=(0, 0, k), Ls=4)
        t = time.time()
        d, tr = tsmc.bmc(ts, P['tx'], 90)
        log('  %-7s A0->ua2 extra %2d: tx %s [%d bits, %.1fs]' % (
            name, k, 'CEX@%s' % d if d is not None else 'none to 90', ts.nbits(), time.time() - t))
        if d is not None:
            wv(ts, tr)


if __name__ == '__main__':
    secs = sys.argv[1:] or ['tb', 'real', 'arbiter', 'fork']
    for s in secs:
        LOG = open(os.path.join(OUT, 'onecorner_%s.txt' % s), 'w')
        t0 = time.time()
        globals()['sec_' + s]()
        log('section %s: %.1fs' % (s, time.time() - t0))
        LOG.close()
