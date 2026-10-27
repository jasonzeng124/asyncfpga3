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

FAST = dict(o6=(45, 56), o5=(42, 55))
SLOW = dict(o6=(100, 124), o5=(121, 152))


def cm(c, k):
    d6 = 56 + c * (124 - 56)
    d5 = 55 + c * (152 - 55)
    return dict(o6=((1 - k) * d6, (1 + k) * d6), o5=((1 - k) * d5, (1 + k) * d5))


CORNERS = [('FAST', FAST), ('SLOW', SLOW), ('CM c=0 k=0.2', cm(0, 0.2)),
           ('CM c=0.5 k=0.2', cm(0.5, 0.2)), ('CM c=1 k=0.2', cm(1, 0.2)),
           ('CM c=0.5 k=0.085', cm(0.5, 0.085))]
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
    for name, cor in CORNERS[:2] + CORNERS[3:4]:
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


def sec_arbiter():
    log('# shipped bd_arbiter, four-phase clients and server, route 1, units ~25 ps.')
    log('# C-12a used rise (2,2) fall (4,5) (mixed). One corner: (2,2) both edges ~ FAST')
    log('# (45-56 ps), (4,5) both edges ~ SLOW (100-124 ps); CM c=0.5 k=0.2: (3,4).')
    for name, lut in (('FAST (2,2)', ((2, 2), (2, 2))), ('SLOW (4,5)', ((4, 5), (4, 5))),
                      ('CM (3,4)', ((3, 4), (3, 4)))):
        def early(k):
            ts, P = arb.arbiter(lut=lut, route=1, a0fork=(0, 0, k))
            t = time.time()
            d, tr = tsmc.bmc(ts, P['owner'], 55)
            log('  %s A0->ua2 extra %2d: owner/early-ack %s [%d bits, %.1fs]' % (
                name, k, 'CEX@%s' % d if d is not None else 'none to 55', ts.nbits(), time.time() - t))
            return d is not None, ts, tr
        lo, hi, best = 0, 20, None
        bad, ts, tr = early(hi)
        if not bad:
            log('  %s: no early ack up to %d' % (name, hi))
            continue
        best = (hi, ts, tr)
        while lo < hi:
            mid = (lo + hi) // 2
            bad, ts, tr = early(mid)
            if bad:
                hi, best = mid, (mid, ts, tr)
            else:
                lo = mid + 1
        log('  => %s: smallest A0->ua2 extra delay with an early ack: %d' % (name, best[0]))
        wv(best[1], best[2])


def sec_arbiter2():
    log('# follow-up: zero-fork owner CEX at SLOW/CM. Is it the fast server (Ls=1)?')
    log('# owner flags an A0 rise while no single grant is high (A0 beats g2 to ua2).')
    for name, lut in (('SLOW (4,5)', ((4, 5), (4, 5))), ('SLOWp (5,5)', ((5, 5), (5, 5))),
                      ('CM (3,4)', ((3, 4), (3, 4)))):
        for Ls in (1, 2, 3, 4):
            ts, P = arb.arbiter(lut=lut, route=1, a0fork=(0, 0, 0), Ls=Ls)
            t = time.time()
            d, tr = tsmc.bmc(ts, P['owner'], 55)
            log('  %s Ls=%d fork 0: owner %s [%.1fs]' % (name, Ls, 'CEX@%s' % d if d is not None else 'none to 55', time.time() - t))
            if d is None:
                for k in range(1, 21):
                    ts, P = arb.arbiter(lut=lut, route=1, a0fork=(0, 0, k), Ls=Ls)
                    d, tr = tsmc.bmc(ts, P['owner'], 55)
                    if d is not None:
                        log('  %s Ls=%d: smallest A0->ua2 extra delay with owner CEX: %d (depth %d)' % (name, Ls, k, d))
                        wv(ts, tr)
                        break
                break


def sec_arbiter3():
    log('# SLOW one corner, deeper BMC (depth 90): the depth-55 search of arbiter2 found')
    log('# no early ack at any extra delay 1..20 for SLOW/SLOWp, which may be depth, not safety.')
    log('# B-style prediction (inertial): early ack iff late >= early + ua2 rise arc,')
    log('# early = 1 + ustate + 1 + ugrant + 1 (route 1 per net).')
    for name, lut, Ls, ks in (('SLOWp (5,5)', ((5, 5), (5, 5)), 1, (14, 16, 17, 18)),
                              ('SLOW (4,5)', ((4, 5), (4, 5)), 2, (12, 14, 16))):
        for k in ks:
            ts, P = arb.arbiter(lut=lut, route=1, a0fork=(0, 0, k), Ls=Ls)
            t = time.time()
            d, tr = tsmc.bmc(ts, P['owner'], 90)
            log('  %s Ls=%d extra %2d: owner %s [%d bits, %.1fs]' % (
                name, Ls, k, 'CEX@%s' % d if d is not None else 'none to 90', ts.nbits(), time.time() - t))
            if d is not None:
                wv(ts, tr)
                break


if __name__ == '__main__':
    secs = sys.argv[1:] or ['tb', 'real', 'arbiter']
    for s in secs:
        LOG = open(os.path.join(OUT, 'onecorner_%s.txt' % s), 'w')
        t0 = time.time()
        globals()['sec_' + s]()
        log('section %s: %.1fs' % (s, time.time() - t0))
        LOG.close()
