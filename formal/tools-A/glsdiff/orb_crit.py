# Float mirror of Formal.Cells.CElemInvolution.orb with the symmetric exp channel
# (Formal.Core.Delay.Involution.expDelay): find the critical runt width s* of a
# self-loop of total delay TLOOP = delta_inf, and compare with the fid resolver's
# noise-free decision point TLOOP - WIN/2.
import math, sys
def mk(Tp, tau):
    def d(T):
        a = 2 - math.exp(-(T + Tp) / tau)
        return None if a <= 0 else Tp + tau * math.log(a)
    return d, Tp + tau * math.log(2)
def outcome(d, dinf, s, N=4000):
    o = [dinf, None]
    x = d(s - dinf)
    if x is None: return 'L'  # outside domain: treat as lost
    o[1] = s + x
    if o[1] <= o[0]: return 'L'          # first pair cancels: the runt never latched
    for n in range(0, N):
        T = o[n] - o[n + 1]
        x = d(T)
        if x is None: return 'L' if n % 2 == 0 else 'H'
        nxt = o[n] + x
        o.append(nxt)
        if nxt <= o[n + 1]:
            # transitions n+1, n+2 cancel; last surviving is n
            return 'H' if n % 2 == 0 else 'L'
    return 'O'
def crit(Tp, tau):
    d, dinf = mk(Tp, tau)
    lo, hi = 1e-6, dinf - 1e-6
    if outcome(d, dinf, lo) != 'L' or outcome(d, dinf, hi) != 'H':
        return None, dinf
    for _ in range(80):
        m = (lo + hi) / 2
        if outcome(d, dinf, m) == 'H': hi = m
        else: lo = m
    return (lo + hi) / 2, dinf
TLOOP = float(sys.argv[1]) if len(sys.argv) > 1 else 424
WIN = 150
print("TLOOP %g  fid noise-free centre TLOOP-WIN/2 = %g" % (TLOOP, TLOOP - WIN / 2))
for tau in (5, 10, 20, 40, 60, 100, 150, 200):
    Tp = TLOOP - tau * math.log(2)
    if Tp <= 0: continue
    c, dinf = crit(Tp, tau)
    d, _ = mk(Tp, tau)
    print("tau %5g Tp %7.2f  delta_inf %.1f  s* %s  (s*/TLOOP %s)  lft=dinf-d(0)=%.2f" %
          (tau, Tp, dinf, "%.2f" % c if c else "-", "%.3f" % (c / dinf) if c else "-", dinf - d(0)))
