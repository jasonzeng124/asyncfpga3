"""arb.py -- bd_arbcell and bd_arbiter (cells/rtl/bd_arb.v) at gate level.

bd_arbcell (bare decision element, what hw/arb_mtbf.v and tb_arb_overlap drive):
    ustate  bd_c2n_set  LUT6 INIT 64'hFFB2_FFB2_FFB2_FFB2
            pins [r1, r2, q, rst, 0, 0]  ->  q          (q = rst + C(r1,~r2))
    ugrant  LUT6_2 INIT 64'h0C0C_0C0C_A0A0_A0A0
            pins [r1, r2, q, 0, 0, 1]   ->  O5 g1 = r1.q,  O6 g2 = r2.~q
bd_arbiter (shipped, with the ack-hold):
    ustate  LUT6_2 INIT 64'hFFF0_FFB2_ACAC_ACAC
            pins [r1, r2, q, rst, A0, 1] ->  O6 q,  O5 R0 = r1.q + r2.~q
    ugrant  as above
    ua1/ua2 bd_c2 (INIT 64'h00E8_...) pins [g_i, A0, A_i, rst]  ->  A_i
Every LUT output is an `inert` channel with separate rise / fall delay
intervals (prjxray min..max); every net after a LUT output is a `win`
transport wire of fixed delay (the route; 0 = none).  Feedback nets are
included.  Ternary variant: lutK + kwin channels.

Time unit: one tick = `tick` ps (default 4).  Arcs from bd_prims_sim.v /
prjxray CLBLL_L.sdf: A6LUT->O6 rise 45..56 fall 100..124; A5LUT->O5 rise
44..55 fall 122..152 (pin I2, the q pin: 52/150 max).
"""
import math
import z3
import cells as C
import tsmc

INIT_C2N_SET = 0xFFB2FFB2FFB2FFB2
INIT_GRANT = 0x0C0C0C0CA0A0A0A0
INIT_ARB_STATE = 0xFFF0FFB2ACACACAC
INIT_C2 = 0x00E800E800E800E8


def ticks(ps, tick, up):
    return max(1, math.ceil(ps / tick) if up else math.floor(ps / tick))


def arcs(tick=4, spread=True):
    """(rise(lo,hi), fall(lo,hi)) in ticks for O6 and O5.  spread=False: max only."""
    def iv(lo, hi):
        if not spread:
            lo = hi
        return (ticks(lo, tick, False), ticks(hi, tick, True))
    o6 = (iv(45, 56), iv(100, 124))
    o5 = (iv(44, 52), iv(122, 150))
    return o6, o5


class Net:
    """Small netlist builder over a TS.  Signals are accessors S -> value."""

    def __init__(self, ts, settled=False):
        self.ts = ts
        self.sig = {}
        self.settled = settled    # start from a quiescent state (all nets
                                  # stable, consistent with the gates)

    def _settle(self, name, f, hist):
        if self.settled:
            def ini(S):
                cs = [S[name] == f(S)]
                cs += [S['%s~%d' % (name, j)] == S[name] for j in range(1, hist)]
                return z3.And(cs)
            self.ts.init(ini)

    def lut(self, name, init, pins, arc):
        ts = self.ts
        f = lambda S: C.lutB(init, [p(S) if callable(p) else p for p in pins])
        C.inert(ts, name, f, arc[0], arc[1])
        self._settle(name, f, 0)
        self.sig[name] = lambda S, n=name: S[n]
        return self.sig[name]

    def wire(self, name, src, d):
        if d == 0:
            self.sig[name] = src
            return src
        C.win(self.ts, name, src, d, d)
        self._settle(name, src, d)
        self.sig[name] = lambda S, n=name: S[n]
        return self.sig[name]


def env_free(ts, names, P):
    """Requests are free binary signals, each level held >= P ticks."""
    for n in names:
        ts.bool(n)
        ts.int(n + '#p', 0, P)
        ts.init(lambda S, n=n: S[n + '#p'] == P)

        def tr(S, N, n=n):
            ch = N[n] != S[n]
            return z3.And(z3.Implies(ch, S[n + '#p'] >= P - 1),
                          N[n + '#p'] == z3.If(ch, 0, z3.If(S[n + '#p'] < P, S[n + '#p'] + 1, P)))
        ts.trans(tr)


def monitors(ts, g1, g2, OVW=64, GW=64):
    """ov = length of the current g1&g2 run; hc1/hc2 = length of the current
    grant-high run; lastw1/2 = width of the last completed grant pulse."""
    ts.int('ov', 0, OVW)
    ts.init(lambda S: S['ov'] == 0)
    ts.trans(lambda S, N: N['ov'] == z3.If(z3.And(g1(S), g2(S)),
                                           z3.If(S['ov'] < OVW, S['ov'] + 1, OVW), 0))
    for i, g in ((1, g1), (2, g2)):
        h, lw = 'hc%d' % i, 'lw%d' % i
        ts.int(h, 0, GW)
        ts.int(lw, 0, GW)
        ts.init(lambda S, h=h, lw=lw: z3.And(S[h] == 0, S[lw] == GW))

        def tr(S, N, g=g, h=h, lw=lw):
            return z3.And(N[h] == z3.If(g(S), z3.If(S[h] < GW, S[h] + 1, GW), 0),
                          N[lw] == z3.If(z3.And(z3.Not(g(S)), S[h] > 0), S[h], S[lw]))
        ts.trans(tr)


def arbcell(tick=4, spread=True, route=0, P=20, rst_len=None, settle=None,
            settled=True, lumped=False, rroute=0, sep=0):
    """Bare bd_arbcell; route = interconnect after every LUT output, in ps.
    settled=True: start from any quiescent state (q either value, all nets
    consistent) with rst = 0, instead of simulating reset from power-up.
    lumped=True: the route is added to every LUT arc inside the inertial
    channel, exactly as bd_prims_sim.v's BD_ROUTE_PS does (no separate
    transport wire).  rroute: transport route on r1/r2 into both LUTs (ps).
    sep: H_SEP -- any two request edges (r1 or r2) are >= sep ticks apart,
    i.e. no two requests move within the cell's aperture."""
    o6, o5 = arcs(tick, spread)
    R = int(round(route / tick))
    RR = int(round(rroute / tick))
    if lumped:
        add = lambda a: ((a[0][0] + R, a[0][1] + R), (a[1][0] + R, a[1][1] + R))
        o6, o5, R = add(o6), add(o5), 0
    ts = tsmc.TS('arbcell_t%d_s%d_R%d_P%d_L%d_RR%d_sep%d' % (tick, spread, R, P, lumped, RR, sep))
    net = Net(ts, settled)
    if settled:
        rst_len, settle = 1, 1
    env_free(ts, ['r1', 'r2'], P)
    if sep:
        ts.int('sep', 0, sep)
        ts.init(lambda S: S['sep'] == sep)

        def sep_tr(S, N):
            ch = z3.Or(N['r1'] != S['r1'], N['r2'] != S['r2'])
            return z3.And(z3.Not(z3.And(N['r1'] != S['r1'], N['r2'] != S['r2'])),
                          z3.Implies(ch, S['sep'] >= sep - 1),
                          N['sep'] == z3.If(ch, 0, z3.If(S['sep'] < sep, S['sep'] + 1, sep)))
        ts.trans(sep_tr)
    r1 = net.wire('r1R', lambda S: S['r1'], RR)
    r2 = net.wire('r2R', lambda S: S['r2'], RR)
    # rst: start in reset long enough to define q, then 0 forever
    loop = o6[0][1] + o6[1][1] + 2 * R
    rl = rst_len or (loop + 2)
    ts.bool('rst')
    ts.int('rc', 0, rl)
    ts.init(lambda S: z3.And(S['rst'] == (not settled), S['rc'] == 0))
    ts.trans(lambda S, N: z3.And(N['rc'] == z3.If(S['rc'] < rl, S['rc'] + 1, rl),
                                 N['rst'] == (S['rc'] < rl - 1)))
    rst = lambda S: S['rst']
    # q's routed net is read by ustate.I2 (feedback) and ugrant.I2
    qR = lambda S: net.sig['qR'](S)
    q = net.lut('q', INIT_C2N_SET, [r1, r2, qR, rst, False, False], o6)
    net.wire('qR', q, R)
    pins = [r1, r2, qR, False, False, True]
    g1 = net.lut('g1', C.o5(INIT_GRANT), pins[:5], o5)
    g2 = net.lut('g2', INIT_GRANT, pins, o6)
    monitors(ts, g1, g2)
    # observation starts once reset has been released and the outputs settled
    ts.bool('live')
    st = settle if settle is not None else rl + o5[1][1] + 1
    ts.int('lc', 0, st)
    ts.init(lambda S: z3.And(S['lc'] == 0, S['live'] == settled))
    ts.trans(lambda S, N: z3.And(N['lc'] == z3.If(S['lc'] < st, S['lc'] + 1, st),
                                 N['live'] == (S['lc'] >= st - 1)))
    ts.show = ['r1', 'r2', 'q', ('qR', lambda r: r.get('qR', r['q'])), 'g1', 'g2', ('ov', lambda r: '#' if r['ov'] else '.')]
    props = {
        'mutex': lambda S: z3.Implies(S['live'], z3.Not(z3.And(g1(S), g2(S)))),
        'ovw': lambda w: (lambda S: z3.Implies(S['live'], S['ov'] < w)),
        'runt': lambda w: (lambda S: z3.Implies(S['live'], z3.And(S['lw1'] >= w, S['lw2'] >= w))),
    }
    return ts, props


def arbcellK(lut=(1, 2), route=1, P=6, tie_stable=None):
    """Ternary bare cell: lutK, kwin channels with one [lo,hi] per LUT (rise
    and fall not distinguished: B-S ternary over-approximation)."""
    ts = tsmc.TS('arbcellK_%s_R%d_P%d' % (lut, route, P))
    env_free(ts, ['r1', 'r2'], P)
    K = lambda n: (lambda S: C.kof(S[n]))
    rl = 2 * (lut[1] + route) + 2
    ts.bool('rst')
    ts.int('rc', 0, rl)
    ts.init(lambda S: z3.And(S['rst'], S['rc'] == 0))
    ts.trans(lambda S, N: z3.And(N['rc'] == z3.If(S['rc'] < rl, S['rc'] + 1, rl),
                                 N['rst'] == (S['rc'] < rl - 1)))
    qR = (lambda S: C.kval(S, 'qR'))
    C.kwin(ts, 'q', lambda S: C.lutK(INIT_C2N_SET, [K('r1')(S), K('r2')(S), qR(S), K('rst')(S), C.F, C.F]),
           lut[0], lut[1])
    C.kwin(ts, 'qR', lambda S: C.kval(S, 'q'), route, route)
    pins = lambda S: [K('r1')(S), K('r2')(S), qR(S), C.F, C.F, C.T]
    C.kwin(ts, 'g1', lambda S: C.lutK(C.o5(INIT_GRANT), pins(S)[:5]), lut[0], lut[1])
    C.kwin(ts, 'g2', lambda S: C.lutK(INIT_GRANT, pins(S)), lut[0], lut[1])
    # tie-stable counter: ticks since r1 = r2 = 1 last started
    ts.int('tie', 0, 64)
    ts.init(lambda S: S['tie'] == 0)
    ts.trans(lambda S, N: N['tie'] == z3.If(z3.And(N['r1'], N['r2']),
                                            z3.If(S['tie'] < 64, S['tie'] + 1, 64), 0))
    ts.bool('live')
    ts.trans(lambda S, N: N['live'] == z3.Or(S['live'], S['rc'] >= rl))
    ts.init(lambda S: z3.Not(S['live']))
    g1 = lambda S: C.kval(S, 'g1')
    g2 = lambda S: C.kval(S, 'g2')
    q = lambda S: C.kval(S, 'q')
    ts.show = ['rst', 'r1', 'r2', ('q', lambda r: C.kfmt(r, 'q')), ('qR', lambda r: C.kfmt(r, 'qR')),
               ('g1', lambda r: C.kfmt(r, 'g1')), ('g2', lambda r: C.kfmt(r, 'g2'))]
    one = lambda v: z3.And(z3.Not(v[0]), v[1])
    props = {
        'mutex11': lambda S: z3.Implies(S['live'], z3.Not(z3.And(one(g1(S)), one(g2(S))))),
        'no_xx': lambda S: z3.Implies(S['live'], z3.Not(z3.And(g1(S)[0], g2(S)[0]))),
        'no_1x': lambda S: z3.Implies(S['live'], z3.Not(z3.Or(z3.And(one(g1(S)), g2(S)[0]),
                                                              z3.And(one(g2(S)), g1(S)[0])))),
        'x_dies': lambda n: (lambda S: z3.Implies(z3.And(S['live'], S['tie'] >= n), z3.Not(q(S)[0]))),
        'q_def': lambda S: z3.Implies(S['live'], z3.Not(q(S)[0])),
    }
    return ts, props


def arbiter(lut=None, route=0, a0fork=(0, 0, 0), fb=0, Lc=1, Ls=1, tick=None):
    """Shipped bd_arbiter with two four-phase clients and a four-phase server.
    lut: ((rise lo,hi),(fall lo,hi)) in ticks for every LUT output (default
    coarse units 1 tick ~ 25 ps: rise (2,2), fall (4,5)).
    route: wire delay on every LUT output net.  a0fork = extra delay of the
    A0 branch to (ustate.I4, ua1.I1, ua2.I1).  fb: C-element feedback wire.
    Lc/Ls: minimum client / server reaction latency (no maximum)."""
    lut = lut or ((2, 2), (4, 5))
    ts = tsmc.TS('arbiter_%s_R%d_A0%s_fb%d' % (lut, route, a0fork, fb))
    net = Net(ts)
    rl = 3 * (lut[1][1] + route + fb) + 2
    ts.bool('rst')
    ts.int('rc', 0, rl)
    ts.init(lambda S: z3.And(S['rst'], S['rc'] == 0))
    ts.trans(lambda S, N: z3.And(N['rc'] == z3.If(S['rc'] < rl, S['rc'] + 1, rl),
                                 N['rst'] == (S['rc'] < rl - 1)))
    rst = lambda S: S['rst']
    for n in ('r1', 'r2', 'A0'):
        ts.bool(n)
        ts.init(lambda S, n=n: z3.Not(S[n]))
    sig = net.sig
    r1 = lambda S: S['r1']
    r2 = lambda S: S['r2']
    A0s = lambda S: sig['A0s'](S)
    qR = lambda S: sig['qR'](S)
    pins_s = [r1, r2, qR, rst, A0s, True]
    q = net.lut('q', INIT_ARB_STATE, pins_s, lut)
    R0 = net.lut('R0', C.o5(INIT_ARB_STATE), pins_s[:5], lut)
    net.wire('qR', q, route)
    net.wire('R0R', R0, route)
    pins_g = [r1, r2, qR, False, False, True]
    g1 = net.lut('g1', C.o5(INIT_GRANT), pins_g[:5], lut)
    g2 = net.lut('g2', INIT_GRANT, pins_g, lut)
    net.wire('g1R', g1, route)
    net.wire('g2R', g2, route)
    A0 = lambda S: S['A0']
    net.wire('A0s', A0, route + a0fork[0])
    net.wire('A0a', A0, route + a0fork[1])
    net.wire('A0b', A0, route + a0fork[2])
    A1fb = lambda S: sig['A1f'](S)
    A2fb = lambda S: sig['A2f'](S)
    A1 = net.lut('A1', INIT_C2, [sig['g1R'], sig['A0a'], A1fb, rst, False, False], lut)
    A2 = net.lut('A2', INIT_C2, [sig['g2R'], sig['A0b'], A2fb, rst, False, False], lut)
    net.wire('A1f', A1, fb)
    net.wire('A2f', A2, fb)
    net.wire('A1R', A1, route)
    net.wire('A2R', A2, route)
    R0R = sig['R0R']
    A1R, A2R = sig['A1R'], sig['A2R']
    # four-phase environment with minimum latencies (counters since the
    # enabling condition became true; no upper bound: the env may stall)
    for n, en, L in (('r1', lambda S: z3.If(S['r1'], A1R(S), z3.Not(A1R(S))), Lc),
                     ('r2', lambda S: z3.If(S['r2'], A2R(S), z3.Not(A2R(S))), Lc),
                     ('A0', lambda S: z3.If(S['A0'], z3.Not(R0R(S)), R0R(S)), Ls)):
        ts.int(n + '#w', 0, L)
        ts.init(lambda S, n=n: S[n + '#w'] == 0)

        def tr(S, N, n=n, en=en, L=L):
            moved = N[n] != S[n]
            ok = S['rc'] >= rl                     # env idle during reset
            return z3.And(
                z3.Implies(moved, z3.And(en(S), S[n + '#w'] >= L - 1, ok)),
                N[n + '#w'] == z3.If(moved, 0, z3.If(en(S), z3.If(S[n + '#w'] < L, S[n + '#w'] + 1, L), 0)))
        ts.trans(tr)
    # protocol monitor: owner of the current server transaction
    ts.int('own', 0, 3)
    for n in ('A0', 'A1', 'A2'):
        ts.bool(n + 'p')
    ts.init(lambda S: z3.And(S['own'] == 0, z3.Not(S['A0p']), z3.Not(S['A1p']), z3.Not(S['A2p'])))

    def mon(S, N):
        rise0 = z3.And(N['A0'], z3.Not(S['A0']))
        fall0 = z3.And(z3.Not(N['A0']), S['A0'])
        who = z3.If(z3.And(g1(S), z3.Not(g2(S))), 1, z3.If(z3.And(g2(S), z3.Not(g1(S))), 2, 3))
        return z3.And(N['own'] == z3.If(rise0, who, z3.If(fall0, 0, S['own'])),
                      N['A0p'] == S['A0'], N['A1p'] == S['A1'], N['A2p'] == S['A2'])
    ts.trans(mon)
    ts.show = ['rst', 'r1', 'r2', 'q', 'g1', 'g2', 'R0', 'A0', 'A0s', 'A0a', 'A0b', 'A1', 'A2', 'own']
    live = lambda S: S['rc'] >= rl
    props = {
        'mutex': lambda S: z3.Implies(live(S), z3.Not(z3.And(g1(S), g2(S)))),
        'ackmutex': lambda S: z3.Implies(live(S), z3.Not(z3.And(S['A1'], S['A2']))),
        'owner': lambda S: z3.Implies(live(S), z3.And(
            S['own'] != 3,
            z3.Implies(z3.And(S['A1'], z3.Not(S['A1p'])), S['own'] == 1),
            z3.Implies(z3.And(S['A2'], z3.Not(S['A2p'])), S['own'] == 2))),
    }
    return ts, props
