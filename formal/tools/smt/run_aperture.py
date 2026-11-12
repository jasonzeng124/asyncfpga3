"""run_aperture.py -- the bare arbcell's aperture: smallest H_SEP (any two
request edges >= sep ticks apart) giving mutual exclusion, transport routes
on every net, prjxray min..max arcs, tick 8 ps.  -> results/arb_aperture.txt
Usage: python3.13 run_aperture.py [route_ps ...]   (default 48)"""
import os
import sys
import time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arb
import tsmc

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results')
LOG = open(os.path.join(OUT, 'arb_aperture.txt'), 'a')


def log(s):
    print(s, flush=True)
    LOG.write(s + '\n')
    LOG.flush()


for route in [int(a) for a in sys.argv[1:]] or [48]:
    log('== route %d ps on every net (q and r1/r2), tick 8 ps, spread arcs' % route)
    lo, hi = 1, 64
    while lo < hi:                       # smallest sep with no cex to depth 50
        mid = (lo + hi) // 2
        ts, P = arb.arbcell(tick=8, spread=True, route=route, rroute=route, P=mid, sep=mid)
        t = time.time()
        d, tr = tsmc.bmc(ts, P['mutex'], 50)
        log('   sep=%2d ticks (%3d ps): %s [%.1fs]' % (mid, mid * 8, 'cex@%d' % d if d is not None else 'no cex to 50', time.time() - t))
        if d is None:
            hi = mid
        else:
            lo = mid + 1
            last = (mid, ts, tr)
    log('   => aperture (bounded, depth 50): sep >= %d ticks = %d ps' % (lo, lo * 8))
    ts, P = arb.arbcell(tick=8, spread=True, route=route, rroute=route, P=lo, sep=lo)
    t = time.time()
    r = tsmc.kind(ts, P['mutex'], 70)
    log('   k-induction at sep=%d: %s [%.1fs]' % (lo, r[:2], time.time() - t))
    if 'last' in dir():
        log('   counterexample at sep=%d:' % last[0])
        log('\n'.join('     ' + l for l in tsmc.wave(last[1], last[2], last[1].show).split('\n')))
