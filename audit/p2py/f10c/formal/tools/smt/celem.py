"""celem.py -- bd_c2 (cells/rtl/bd_ce.v) as a feedback LUT under bounded delays.

    LUT6 #(.INIT(64'h00E8_00E8_00E8_00E8)) u (.I0(a), .I1(b), .I2(q), .I3(rst),
                                            .I4(0), .I5(0), .O(q));

Gate model (binary):
    e(t)  = lutB(INIT, [a(t), b(t), qp(t), rst(t), 0, 0])   excitation
    O     = chan_LUT(e)   delay in [dl_lo, dl_hi]            LUT output pin
    qp    = chan_W(O)     delay in [dw_lo, dw_hi]            routed feedback at I2
Channel kind: win | fifo | inert (see cells.py).  Power-up: every channel's
history/state is arbitrary.

Environment (H_ENV_PULSE(W), H_RST(R)):
    rst = 1 on ticks [0, R-1], may fall at R or later, never rises again.
    a, b are free, EXCEPT: when the ideal C-element z changes (an enabling
    combination a = b = v != z appears, or reset releases into one), a and b
    hold for W ticks.
Spec monitor: z(t) = rst(t) ? 0 : maj(a(t), b(t), z(t-1)); cnt = ticks since
z last changed (saturating at dl_hi).
Properties:
    P_follow : cnt >= dl_hi  ->  O == z        (settles within the LUT delay
                                                 and holds)
    P_mono   : O == O(t-1)  or  O == z          (O never moves away from the
                                                 spec value: no hazard; checked
                                                 from tick dl_hi on, i.e. once
                                                 the power-up history is flushed)
Ternary variant (kleene=True): every signal is {0,1,X}, the LUT is lutK, the
channels are kwin; env still binary unless xin > 0, in which case every
input change may pass through X for up to xin ticks (a slow / runt edge).
P_follow then also demands O definite.
"""
import z3
import cells as C
import tsmc

INIT_C2 = 0x00E800E800E800E8


def maj(a, b, c):
    return z3.Or(z3.And(a, b), z3.And(a, c), z3.And(b, c))


def build(kind='win', dl=(1, 2), dw=(1, 2), W=4, R=None, kleene=False,
          xin=0, env='pulse', E=None, obs='first'):
    """env='pulse': H_ENV_PULSE(W).  env='4ph': two four-phase clients that
    move only after seeing O at their own value; E = min ticks between
    observing the ack and moving (H_ENV_LATENCY).  obs='first': the latency
    counts from the client's FIRST sight of the ack (B's H_ACK); obs='stable':
    the client must see the ack E ticks in a row (a glitch restarts it)."""
    Dmax = dl[1] + dw[1]
    if R is None:
        R = Dmax
    ts = tsmc.TS('c2_%s_%s_%s_W%s_R%s_%s%s%s%s%s' % (kind, dl, dw, W, R, env, E if env == '4ph' else '', obs if env == '4ph' else '',
                                              '_K' if kleene else '',
                                              '_x%d' % xin if xin else ''))
    for n in ('a', 'b', 'rst', 'z', 'Op'):
        ts.bool(n)
    ts.int('cnt', 0, dl[1])
    ts.int('rc', 0, R)
    ts.int('hold', 0, max(W or 1, 1))
    if env == '4ph':
        for n in ('a', 'b'):
            ts.int(n + 'w', 0, E)    # ticks since this client saw its ack
    if kleene and xin:
        for n in ('a', 'b'):
            ts.bool(n + 'X')         # input currently in a slow edge (X)
            ts.int(n + 'xc', 0, xin)

    # --- environment & monitor ---
    ts.init(lambda S: z3.And(S['rst'], S['rc'] == 0, z3.Not(S['z']),
                             S['cnt'] == 0, S['hold'] == 0))

    def env_tr(S, N):
        cs = [z3.Implies(N['rst'], S['rst']),
              z3.Implies(z3.Not(N['rst']), S['rc'] >= R - 1),
              N['rc'] == z3.If(S['rc'] < R, S['rc'] + 1, R)]
        zn = z3.If(N['rst'], False, maj(N['a'], N['b'], S['z']))
        cs.append(N['z'] == zn)
        changed = N['z'] != S['z']
        cs.append(N['cnt'] == z3.If(changed, 0, z3.If(S['cnt'] < dl[1], S['cnt'] + 1, dl[1])))
        if env == 'pulse':
            cs.append(z3.Implies(S['hold'] > 0, z3.And(N['a'] == S['a'], N['b'] == S['b'])))
            cs.append(N['hold'] == z3.If(z3.And(changed, z3.Not(N['rst'])), W - 1,
                                         z3.If(S['hold'] > 0, S['hold'] - 1, 0)))
        else:
            cs.append(N['hold'] == 0)
            # four-phase client: may toggle its input only once the C-element
            # output O (as the client sees it, at the LUT output) equals its
            # input, and only E ticks after first seeing that.
            for n in ('a', 'b'):
                seen = S['O'] == S[n] if not kleene else \
                    z3.And(z3.Not(S['O.x']), S['O.v'] == S[n])
                if obs == 'stable':     # must see the ack E ticks in a row
                    sighted = seen
                else:                   # 'first': first glimpse counts (B's H_ACK)
                    sighted = z3.Or(seen, S[n + 'w'] > 0)
                moved = N[n] != S[n]
                cs.append(N[n + 'w'] == z3.If(moved, 0, z3.If(sighted, z3.If(S[n + 'w'] < E, S[n + 'w'] + 1, E), 0)))
                cs.append(z3.Implies(moved, z3.And(sighted, S[n + 'w'] >= E - 1)))
        return z3.And(cs)
    ts.trans(env_tr)
    if env == '4ph':
        ts.init(lambda S: z3.And(z3.Not(S['a']), z3.Not(S['b']), S['aw'] == 0, S['bw'] == 0))

    if not kleene:
        def e(S):
            return C.lutB(INIT_C2, [S['a'], S['b'], S['qp'], S['rst'], False, False])
        C.chan(ts, kind, 'O', e, dl[0], dl[1])
        C.chan(ts, kind, 'qp', lambda S: S['O'], dw[0], dw[1])
        ts.trans(lambda S, N: N['Op'] == S['O'])
        ts.init(lambda S: S['Op'] == S['O'])
        Pf = lambda S: z3.Implies(S['cnt'] >= dl[1], S['O'] == S['z'])
        Pm = lambda S: z3.Or(S['rc'] < min(dl[1], R), S['O'] == S['Op'], S['O'] == S['z'])
        ts.show = ['rst', 'a', 'b', 'z', 'O', 'qp', 'cnt']
    else:
        def pin(S, n):
            if xin:
                return (S[n + 'X'], z3.And(z3.Not(S[n + 'X']), S[n]))
            return C.kof(S[n])

        def e(S):
            return C.lutK(INIT_C2, [pin(S, 'a'), pin(S, 'b'), C.kval(S, 'qp'),
                                    C.kof(S['rst']), C.F, C.F])
        C.kwin(ts, 'O', e, dl[0], dl[1])
        C.kwin(ts, 'qp', lambda S: C.kval(S, 'O'), dw[0], dw[1])
        C.kvar(ts, 'Opk')
        ts.trans(lambda S, N: C.keq(C.kval(N, 'Opk'), C.kval(S, 'O')))
        ts.trans(lambda S, N: N['Op'] == S['O.v'])
        ts.init(lambda S: C.keq(C.kval(S, 'Opk'), C.kval(S, 'O')))
        if xin:
            # an input change may be preceded by up to xin ticks of X on that
            # pin (the edge passes through the intermediate band).  a/b hold
            # the TARGET value; aX marks the pin as X this tick.
            def xtr(S, N):
                cs = []
                for n in ('a', 'b'):
                    # X only while counting, at most xin ticks, and only
                    # right before the binary value changes
                    cs.append(z3.Implies(N[n + 'X'], N[n + 'xc'] == S[n + 'xc'] + 1))
                    cs.append(z3.Implies(z3.Not(N[n + 'X']), N[n + 'xc'] == 0))
                    cs.append(z3.Implies(z3.And(S[n + 'X'], z3.Not(N[n + 'X'])),
                                         N[n] != S[n]))
                    cs.append(z3.Implies(N[n + 'X'], N[n] == S[n]))
                    cs.append(z3.Implies(S['hold'] > 0, z3.Not(N[n + 'X'])))
                return z3.And(cs)
            ts.trans(xtr)
            ts.init(lambda S: z3.And(z3.Not(S['aX']), z3.Not(S['bX']),
                                     S['axc'] == 0, S['bxc'] == 0))
        Pf = lambda S: z3.Implies(S['cnt'] >= dl[1],
                                  z3.And(z3.Not(S['O.x']), S['O.v'] == S['z']))
        Pm = lambda S: z3.Or(S['rc'] < min(dl[1], R), C.keq(C.kval(S, 'O'), C.kval(S, 'Opk')),
                             C.keq(C.kval(S, 'O'), C.kof(S['z'])))
        ts.show = ['rst', 'a', 'b', 'z',
                   ('O', lambda r: C.kfmt(r, 'O')), ('qp', lambda r: C.kfmt(r, 'qp')), 'cnt']
        if xin:
            ts.show[1:3] = [('a', lambda r: 'X' if r['aX'] else ('1' if r['a'] else '_')),
                            ('b', lambda r: 'X' if r['bX'] else ('1' if r['b'] else '_'))]
    return ts, {'follow': Pf, 'mono': Pm}
