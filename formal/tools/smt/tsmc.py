"""tsmc.py -- a tiny transition-system model checker on z3.

A model is a TS: named state variables (Bool, or bounded Int), an initial
predicate and a transition relation over (S, N) = (current, next) dicts of
z3 terms.  There are no separate inputs: every nondeterministic choice
(environment moves, per-transition delays) is an unconstrained next-state
variable restricted by the transition relation.

Engines
  bmc(ts, prop, k)          bounded model checking, depth 0..k, returns a trace
  kind(ts, prop, kmax)      k-induction with simple-path constraints
                            (complete for finite state: proves for all depths)
  spacer(ts, prop, tmo)     IC3/PDR via z3's Spacer CHC engine (unbounded)

prop is a function S -> z3 Bool over state variables only.
"""
import time
import z3


class TS:
    def __init__(self, name):
        self.name = name
        self.vars = {}          # name -> ('b',) | ('i', lo, hi)
        self.inits = []         # fn S -> expr
        self.transs = []        # fn S, N -> expr
        self.show = []          # signals to print in traces (names or (label, fn))

    def bool(self, n):
        assert n not in self.vars, n
        self.vars[n] = ('b',)
        return n

    def int(self, n, lo, hi):
        assert n not in self.vars, n
        self.vars[n] = ('i', lo, hi)
        return n

    def init(self, f):
        self.inits.append(f)

    def trans(self, f):
        self.transs.append(f)

    # -- encoding ---------------------------------------------------------
    def mk(self, sfx):
        S = {}
        for n, k in self.vars.items():
            S[n] = z3.Bool(n + sfx) if k[0] == 'b' else z3.Int(n + sfx)
        return S

    def rng(self, S):
        cs = []
        for n, k in self.vars.items():
            if k[0] == 'i':
                cs += [S[n] >= k[1], S[n] <= k[2]]
        return z3.And(cs) if cs else z3.BoolVal(True)

    def I(self, S):
        return z3.And([self.rng(S)] + [f(S) for f in self.inits])

    def T(self, S, N):
        return z3.And([self.rng(N)] + [f(S, N) for f in self.transs])

    def distinct(self, A, B):
        return z3.Or([A[n] != B[n] for n in self.vars])

    def nbits(self):
        import math
        b = 0
        for k in self.vars.values():
            b += 1 if k[0] == 'b' else max(1, math.ceil(math.log2(k[2] - k[1] + 1)))
        return b


def _trace(ts, m, Ss):
    rows = []
    for S in Ss:
        row = {}
        for n in ts.vars:
            v = m.eval(S[n], model_completion=True)
            row[n] = z3.is_true(v) if ts.vars[n][0] == 'b' else v.as_long()
        rows.append(row)
    return rows


def bmc(ts, prop, k, start=0):
    """Return (depth, trace) of the shortest violation <= k, or (None, None)."""
    s = z3.Solver()
    Ss = [ts.mk('@0')]
    s.add(ts.I(Ss[0]))
    for i in range(k + 1):
        if i > 0:
            Ss.append(ts.mk('@%d' % i))
            s.add(ts.T(Ss[i - 1], Ss[i]))
        if i < start:
            continue
        s.push()
        s.add(z3.Not(prop(Ss[i])))
        r = s.check()
        if r == z3.sat:
            tr = _trace(ts, s.model(), Ss)
            s.pop()
            return i, tr
        s.pop()
    return None, None


def kind(ts, prop, kmax, verbose=False):
    """k-induction.  Returns ('proved', k) | ('cex', depth, trace) | ('unknown', kmax)."""
    base = z3.Solver()
    step = z3.Solver()
    B = [ts.mk('@b0')]
    base.add(ts.I(B[0]))
    P = [ts.mk('@s0')]
    step.add(ts.rng(P[0]))
    for k in range(kmax + 1):
        # base case: no violation at depth k
        if k > 0:
            B.append(ts.mk('@b%d' % k))
            base.add(ts.T(B[k - 1], B[k]))
        base.push()
        base.add(z3.Not(prop(B[k])))
        if base.check() == z3.sat:
            tr = _trace(ts, base.model(), B)
            return ('cex', k, tr)
        base.pop()
        # inductive step: k+1 states P0..Pk, prop on P0..P(k-1), not prop on Pk
        if k > 0:
            P.append(ts.mk('@s%d' % k))
            step.add(ts.T(P[k - 1], P[k]))
            step.add(prop(P[k - 1]))
            for j in range(k):
                step.add(ts.distinct(P[j], P[k]))
        step.push()
        step.add(z3.Not(prop(P[k])))
        r = step.check()
        step.pop()
        if verbose:
            print('  k=%d step %s' % (k, r))
        if r == z3.unsat:
            return ('proved', k)
    return ('unknown', kmax)


def spacer(ts, prop, timeout_s=120):
    """IC3/PDR via Spacer.  Returns 'proved' | 'cex' | 'unknown'."""
    names = list(ts.vars)
    sorts = [z3.BoolSort() if ts.vars[n][0] == 'b' else z3.IntSort() for n in names]
    fp = z3.Fixedpoint()
    fp.set(engine='spacer')
    fp.set('timeout', int(timeout_s * 1000))
    Inv = z3.Function('Inv_' + ts.name, *sorts, z3.BoolSort())
    fp.register_relation(Inv)
    S = ts.mk('_c')
    N = ts.mk('_n')
    allv = [S[n] for n in names] + [N[n] for n in names]
    fp.declare_var(*allv)
    fp.rule(Inv(*[S[n] for n in names]), ts.I(S))
    fp.rule(Inv(*[N[n] for n in names]),
            [Inv(*[S[n] for n in names]), ts.T(S, N)])
    try:
        r = fp.query(z3.And(Inv(*[S[n] for n in names]), z3.Not(prop(S))))
    except z3.Z3Exception as e:
        return 'unknown(%s)' % e
    if r == z3.unsat:
        return 'proved'
    if r == z3.sat:
        return 'cex'
    return 'unknown'


def prove(ts, prop, kmax=40, bmc_k=None, use_spacer=True, spacer_tmo=120):
    """BMC + k-induction (+ Spacer if k-induction does not close).  Returns dict."""
    t0 = time.time()
    out = {'model': ts.name, 'bits': ts.nbits()}
    r = kind(ts, prop, kmax)
    out['kind'] = r[0]
    if r[0] == 'proved':
        out['k'] = r[1]
    elif r[0] == 'cex':
        out['depth'] = r[1]
        out['trace'] = r[2]
    out['t_kind'] = round(time.time() - t0, 2)
    if r[0] == 'unknown' and use_spacer:
        t1 = time.time()
        out['spacer'] = spacer(ts, prop, spacer_tmo)
        out['t_spacer'] = round(time.time() - t1, 2)
    out['t'] = round(time.time() - t0, 2)
    return out


def verdict(out):
    if out['kind'] == 'proved':
        return 'PROVED (k-induction, k=%d)' % out['k']
    if out['kind'] == 'cex':
        return 'CEX at depth %d' % out['depth']
    if out.get('spacer') == 'proved':
        return 'PROVED (Spacer/IC3)'
    if out.get('spacer') == 'cex':
        return 'CEX (Spacer)'
    return 'UNKNOWN'


def wave(ts, tr, sigs, fmt=None):
    """Print a trace as text waveforms.  sigs: list of names or (label, fn(row))."""
    lines = []
    T = len(tr)
    hdr = ''.join('%d' % (t % 10) for t in range(T))
    lines.append('%-10s %s' % ('t', hdr))
    for s in sigs:
        if isinstance(s, tuple):
            lab, f = s
        else:
            lab, f = s, (lambda r, s=s: r[s])
        cs = []
        for r in tr:
            v = f(r)
            if v is True:
                cs.append('1')
            elif v is False:
                cs.append('_')
            elif isinstance(v, str):
                cs.append(v)
            else:
                cs.append(str(v % 36) if v < 10 else chr(ord('a') + v - 10) if v < 36 else '#')
        lines.append('%-10s %s' % (lab, ''.join(cs)))
    return '\n'.join(lines)
