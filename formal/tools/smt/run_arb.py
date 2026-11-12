"""run_arb.py -- arbiter checks.  Usage: python3.13 run_arb.py [section ...]

sections: tb (bare cell, bd_prims_sim semantics), real (bare cell, transport
routes), kleene (ternary bare cell), arbiter (shipped bd_arbiter, A0 fork).
Results: stdout and results/arb_<section>.txt
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


def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    LOG.write(s + '\n')
    LOG.flush()


def wv(ts, tr, extra=()):
    log('\n'.join('     ' + l for l in tsmc.wave(ts, tr, list(ts.show) + list(extra)).split('\n')))


def maxov(mk, depth, wmax=40):
    """Largest overlap run reachable within depth (bounded)."""
    best = 0
    for w in range(1, wmax + 1):
        ts, P = mk()
        d, tr = tsmc.bmc(ts, P['ovw'](w), depth)
        if d is None:
            break
        best = w
    return best


def minrunt(mk, depth, wmax=40):
    """Smallest completed grant pulse width reachable within depth."""
    for w in range(1, wmax + 1):
        ts, P = mk()
        d, tr = tsmc.bmc(ts, P['runt'](w), depth)
        if d is not None:
            return w - 1, ts, tr
    return None, None, None


def sec_tb():
    log('# bare bd_arbcell, bd_prims_sim.v semantics: route lumped into the inertial')
    log('# LUT arc (BD_ROUTE_PS), fixed max arcs, r1/r2 straight from registers.')
    log('# header claim: overlap iff route < 16 ps (124 vs 56+52); tb_arb_overlap: 89 at 0, 0 at 354')
    for tick, routes, depth in ((4, (0, 8, 12, 16, 20), 80), (8, (16, 24, 48), 60)):
        for route in routes:
            mk = lambda: arb.arbcell(tick=tick, spread=False, route=route, P=40 if tick == 4 else 20, lumped=True)
            ts, P = mk()
            t = time.time()
            if tick == 8 or route >= 16:
                r = tsmc.kind(ts, P['mutex'], 60)
                res = r[0] if r[0] != 'cex' else 'cex@%d' % r[1]
                if r[0] == 'proved':
                    res += ' (k=%d)' % r[1]
                tr = r[2] if r[0] == 'cex' else None
            else:
                d, tr = tsmc.bmc(ts, P['mutex'], depth)
                res = 'cex@%s' % d if d is not None else 'no cex to depth %d' % depth
            log('  tick=%dps route=%3dps mutex: %-22s [%d bits, %.1fs]' % (tick, route, res, ts.nbits(), time.time() - t))
            if tr is not None and route == 0 and tick == 4:
                wv(ts, tr)
                w = maxov(mk, depth)
                log('    max overlap run (bounded, depth %d): %d ticks = %d ps' % (depth, w, w * tick))


def sec_real():
    log('# bare bd_arbcell, transport routes on every net (q, and r1/r2 into both LUTs),')
    log('# prjxray min..max arcs (spread), tick 8 ps, free-running requests (P = min level time)')
    tick = 8
    for route in (0, 48, 100):
        mk = lambda sep=0, P=50: arb.arbcell(tick=tick, spread=True, route=route, rroute=route, P=P, sep=sep)
        ts, P = mk()
        d, tr = tsmc.bmc(ts, P['mutex'], 60)
        log('== route %d ps on every net: free env mutex: %s' % (route, 'cex@%s' % d if d is not None else 'none to 60'))
        if d is not None:
            wv(ts, tr)
        w = maxov(lambda: mk(), 60)
        log('   max overlap run (bounded, depth 60): %d ticks = %d ps' % (w, w * tick))
        m, ts2, tr2 = minrunt(lambda: mk(), 60)
        log('   narrowest completed grant pulse (bounded, depth 60): %s ticks' % m)
        if tr2 is not None:
            wv(ts2, tr2, [('lw1', lambda r: r['lw1'] if r['lw1'] < 36 else 35), ('lw2', lambda r: r['lw2'] if r['lw2'] < 36 else 35)])
        # aperture: smallest request separation that gives mutual exclusion
        last = None
        for sep in range(2, 61, 2):
            ts, P = mk(sep=sep, P=sep)
            d, tr = tsmc.bmc(ts, P['mutex'], 70)
            if d is None:
                t = time.time()
                r = tsmc.kind(ts, P['mutex'], 80)
                log('   H_SEP(%d ticks = %d ps): no cex to 70; k-induction: %s [%.1fs]' % (sep, sep * tick, r[:2], time.time() - t))
                if last is not None:
                    log('   cex at sep=%d:' % last[0])
                    wv(last[1], last[2])
                break
            last = (sep, ts, tr)


def sec_kleene():
    log('# ternary bare cell (lutK, kwin channels [1,2] per LUT, route 1, env free, P=6)')
    ts, P = arb.arbcellK()
    for name, what in (('mutex11', 'never g1 = g2 = definite 1'),
                       ('no_1x', 'a definite 1 grant never meets an X on the other'),
                       ('no_xx', 'X never on both grants'),
                       ('q_def', 'q never X after reset')):
        t = time.time()
        r = tsmc.prove(ts, P[name], kmax=40, spacer_tmo=120)
        log('  %-8s (%s): %s [%.1fs]' % (name, what, tsmc.verdict(r), time.time() - t))
        if r['kind'] == 'cex':
            wv(ts, r['trace'])
    for n in (10, 30):
        d, tr = tsmc.bmc(ts, P['x_dies'](n), 50)
        log('  X on q survives %d ticks of a stable tie r1 = r2 = 1: %s' % (n, 'REACHABLE (depth %d)' % d if d else 'not within 50'))
        if d and n == 30:
            wv(ts, tr)


def sec_arbiter():
    log('# shipped bd_arbiter, two four-phase clients + four-phase server, LUT rise (2,2) fall (4,5),')
    log('# route 1 on every LUT output net, A0 fork: extra delay on the branch to ua2 (B: H_A0_FORK)')
    # binary search for the smallest extra delay with an early ack (monotone in k)
    def early(k):
        ts, P = arb.arbiter(route=1, a0fork=(0, 0, k))
        t = time.time()
        d, tr = tsmc.bmc(ts, P['owner'], 55)
        log('  A0->ua2 extra delay %2d: owner/early-ack %s [%d bits, %.1fs]' % (k, 'cex@%s' % d if d is not None else 'none to 55', ts.nbits(), time.time() - t))
        return d is not None, ts, tr
    lo, hi = 0, 14          # early(hi) known true (cex@47 in a first run)
    best = None
    while lo < hi:
        mid = (lo + hi) // 2
        bad, ts, tr = early(mid)
        if bad:
            hi, best = mid, (mid, ts, tr)
        else:
            lo = mid + 1
    if best is None:
        best = (hi,) + early(hi)[1:]
    log('  => smallest A0->ua2 extra delay giving an early ack: %d ticks (B: early iff late > early;'
        ' early = 1+4+1+2+1 = 9, late = 1 + k)' % best[0])
    wv(best[1], best[2])
    for fork in ((0, 0, 0),):
        ts, P = arb.arbiter(route=1, a0fork=fork)
        for name in ('mutex', 'ackmutex', 'owner'):
            t = time.time()
            r = tsmc.kind(ts, P[name], 50)
            log('  fork %s %s: k-induction %s [%.1fs]' % (fork, name, r[:2], time.time() - t))
            if r[0] == 'unknown':
                t = time.time()
                log('     spacer: %s [%.1fs]' % (tsmc.spacer(ts, P[name], 600), time.time() - t))


if __name__ == '__main__':
    secs = sys.argv[1:] or ['tb', 'real', 'kleene', 'arbiter']
    for s in secs:
        LOG = open(os.path.join(OUT, 'arb_%s.txt' % s), 'w')
        t0 = time.time()
        globals()['sec_' + s]()
        log('section %s: %.1fs' % (s, time.time() - t0))
        LOG.close()
