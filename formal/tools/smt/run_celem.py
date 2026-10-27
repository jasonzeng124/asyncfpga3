"""run_celem.py -- sweeps for bd_c2.  Usage: python3.13 run_celem.py [pulse] [4ph] [kleene] [quick]

For each channel kind and delay bound set:
  * smallest pulse width W for which P_follow (resp. P_mono) is PROVED
    (k-induction, Spacer as fallback), and the counterexample at W-1;
  * smallest reset length R (with W large);
  * four-phase environment: smallest ack-to-move latency E;
  * ternary variant: same W sweep; power-up X; slow edges (X inputs).
Results go to stdout and results/celem_<sections>.txt.
"""
import os
import sys
import time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import celem
import tsmc

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results')
os.makedirs(OUT, exist_ok=True)
SECS = [a for a in sys.argv[1:] if a in ('pulse', '4ph', 'kleene')] or ['pulse', '4ph', 'kleene']
LOG = open(os.path.join(OUT, 'celem_%s.txt' % '_'.join(SECS)), 'w')
DELAYS = [((1, 1), (1, 1)), ((1, 2), (1, 2)), ((2, 3), (1, 3)), ((1, 3), (2, 2)),
          ((2, 2), (3, 3))]


def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    LOG.write(s + '\n')
    LOG.flush()


def sweep(param, lo, hi, mk, prop, kmax=40, show=True, tmo=120):
    """Smallest value of param in [lo,hi] that proves prop; logs the cex below."""
    last = None
    for v in range(lo, hi + 1):
        ts, P = mk(v)
        r = tsmc.prove(ts, P[prop], kmax=kmax, spacer_tmo=tmo)
        vd = tsmc.verdict(r)
        if vd.startswith('PROVED'):
            log('   %s=%d %s: %s  [%d state bits, %.2fs]' % (param, v, prop, vd, r['bits'], r['t']))
            if last is not None and show:
                log('   counterexample at %s=%d (depth %d):' % (param, v - 1, last[1]['depth']))
                log('\n'.join('     ' + l for l in tsmc.wave(last[0], last[1]['trace'], last[0].show).split('\n')))
            return v
        if vd.startswith('CEX'):
            last = (ts, r)
            continue
        log('   %s=%d %s: %s [%.2fs]' % (param, v, prop, vd, r['t']))
        return None
    log('   %s: no proof up to %d' % (param, hi))
    return None


def sec_pulse(delays):
    table = []
    log('# bd_c2: minimum pulse width W (H_ENV_PULSE) per channel kind')
    log('# B (CElemTiming.lean, WinDelay): W >= Dmax = dl_hi + dw_hi is sufficient, and tight for fixed delays')
    for kind in ('win', 'fifo', 'inert'):
        for dl, dw in delays:
            Dmax = dl[1] + dw[1]
            log('== %s dl=%s dw=%s Dmax=%d' % (kind, dl, dw, Dmax))
            wf = sweep('W', 1, Dmax + 4, lambda W: celem.build(kind, dl, dw, W=W), 'follow')
            wm = sweep('W', 1, Dmax + 4, lambda W: celem.build(kind, dl, dw, W=W), 'mono',
                       show=False, kmax=25, tmo=30)
            rr = sweep('R', 1, Dmax + 4, lambda R: celem.build(kind, dl, dw, W=Dmax + 2, R=R), 'follow', show=False)
            table.append((kind, dl, dw, Dmax, wf, wm, rr))
    log('\n# summary: kind dl dw Dmax  W_follow W_mono R_min   (None = no proof: cex at all W, or UNKNOWN)')
    for row in table:
        log('  %-5s %s %s %2d   %s %s %s' % row)


def sec_4ph(delays):
    log('# four-phase environment (two clients, latency >= E after seeing the ack on O)')
    log('# B (c2_four_phase): sufficient E >= dw_hi + (dl_hi - dl_lo)')
    for kind in ('win', 'fifo', 'inert'):
        for dl, dw in delays:
            Eb = dw[1] + dl[1] - dl[0]
            log('== %s dl=%s dw=%s  B-bound E=%d' % (kind, dl, dw, Eb))
            for obs in ('first', 'stable'):
                e = sweep('E', 1, Eb + 2, lambda E: celem.build(kind, dl, dw, env='4ph', E=E, W=1, obs=obs),
                          'follow', kmax=30, tmo=30)
                log('   => E_min(%s) follow=%s (B bound %d)' % (obs, e, Eb))


def sec_kleene(delays):
    log('# ternary (Kleene) variant, kwin channels, binary env')
    for dl, dw in delays:
        Dmax = dl[1] + dw[1]
        log('== K dl=%s dw=%s Dmax=%d' % (dl, dw, Dmax))
        sweep('W', 1, Dmax + 4, lambda W: celem.build('win', dl, dw, W=W, kleene=True), 'follow')
        sweep('R', 1, Dmax + 4, lambda R: celem.build('win', dl, dw, W=Dmax + 2, R=R, kleene=True), 'follow', show=False)
    log('\n# ternary, slow input edges: each input change may be X for up to xin ticks first')
    for dl, dw in delays[:3]:
        Dmax = dl[1] + dw[1]
        for xin in (1, 2):
            log('== K dl=%s dw=%s xin=%d' % (dl, dw, xin))
            sweep('W', 1, Dmax + 6, lambda W: celem.build('win', dl, dw, W=W, kleene=True, xin=xin), 'follow')


if __name__ == '__main__':
    t0 = time.time()
    d = DELAYS[:2] if 'quick' in sys.argv else DELAYS
    for s in SECS:
        {'pulse': sec_pulse, '4ph': sec_4ph, 'kleene': sec_kleene}[s](d)
    log('\ntotal %.1fs' % (time.time() - t0))
