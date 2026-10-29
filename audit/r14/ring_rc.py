# audit r14: independent physical model of the C(r1,~r2) buffer loop after r2 arrives.
# f = 1 during the set runt [0,s); afterwards f = fb = comparator output delayed by Dp.
# Channel: first-order RC (tau) + ideal comparator at 0.5 + pure delay Dp, so an
# isolated edge takes tau*ln2 + Dp = TLOOP. Optional rise/fall asymmetry via
# comparator threshold vth (vth != 0.5 -> delta_up != delta_dn).
# Integrates exactly per step (exp update). Returns final settled value.
import math, sys
def run(s, TLOOP, tau, vth=0.5, dt=0.25, laps=400):
    du = -tau*math.log(1-vth); dd = -tau*math.log(vth)
    Dp = TLOOP - 0.5*(du+dd)           # mean loop delay = TLOOP
    n_d = int(round(Dp/dt))
    buf = [0]*n_d                       # comparator history (delay line)
    y = 0.0; c = 0; i = 0; edges = 0
    N = int((laps*TLOOP)/dt)
    a = math.exp(-dt/tau)
    for k in range(N):
        t = k*dt
        fb = buf[k % n_d]
        f = 1 if t < s else fb
        y = f + (y - f)*a
        cn = 1 if y > vth else 0
        if cn != c: edges += 1
        c = cn
        buf[k % n_d] = c
        if t > s + 3*TLOOP and k % (n_d) == 0:
            pass
    # settled? check whole delay line constant
    if all(b == buf[0] for b in buf) and c == buf[0]:
        return buf[0], edges
    return None, edges
def sstar(TLOOP, tau, vth=0.5):
    lo, hi = 1.0, TLOOP-1.0
    rlo, _ = run(lo, TLOOP, tau, vth); rhi, _ = run(hi, TLOOP, tau, vth)
    assert rlo == 0 and rhi == 1, (rlo, rhi)
    for _ in range(14):
        m = 0.5*(lo+hi); r, _ = run(m, TLOOP, tau, vth)
        if r == 1: hi = m
        elif r == 0: lo = m
        else: return m, 'unsettled'
    return 0.5*(lo+hi), ''
for TL in (424, 624):
    for tau in (40, 100, 150, 200):
        s, note = sstar(TL, tau)
        print("TLOOP=%d tau=%d s*=%.1f s*/TLOOP=%.3f %s" % (TL, tau, s, s/TL, note), flush=True)
for vth in (0.4, 0.6):
    s, note = sstar(424, 150, vth)
    print("asym vth=%.1f TLOOP=424 tau=150 s*=%.1f s*/TLOOP=%.3f %s" % (vth, s, s/424, note), flush=True)
