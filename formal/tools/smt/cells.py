"""cells.py -- LUT semantics and delay channels for tsmc transition systems.

LUTs (real INIT, real pin map, I0 = LSB of the address):
  lutB(init, pins)     binary: the INIT bit addressed by the pins
  lutK(init, pins)     Kleene closure: 1 / 0 if every INIT entry consistent with
                       the ternary pins is 1 / 0, else X (shard B's lutK,
                       hypothesis H_KLEENE_LUT)
  O5 of a LUT6_2 = lower 32 bits over I0..I4 (I5 tied 1 on these cells);
  O6 = full 64-bit table.
A pin is a z3 Bool / Python bool (binary) or a ternary pair (x, v) of z3 Bools
or Python bools (x = 'not a valid level'; v meaningful only when not x).

Delay channels (each creates state in the TS; x is a function S -> value, the
channel input at the current tick; the channel output is a state variable):
  win     y(t) = x(t-d(t)), d(t) in [lo,hi] chosen afresh every tick
          (shard B's WinDelay: non-FIFO bounded pure delay, the weakest).
  fifo    same, but the sample index is monotone (d(t+1) <= d(t)+1): an
          order-preserving time warp; every edge delayed by its own d in
          [lo,hi]; pulses shorter than hi-lo can be swallowed.
  inert   per-transition delay with separate rise/fall bounds: when x != y a
          counter runs; y may take x once it reaches lo_edge and must by
          hi_edge; a pulse that ends before y moved is lost (inertial with a
          nondeterministic threshold in [lo,hi]).
  kwin    ternary window: y(t) = join{x(s) : s in [t-hi, t-lo]} (X unless the
          whole window agrees): the Brzozowski-Seger style ternary
          over-approximation of a bounded-delay wire.  Deterministic.
"""
import itertools
import z3

T = (False, True)    # ternary 1
F = (False, False)   # ternary 0
X = (True, False)    # ternary X


def _isconst(p):
    return isinstance(p, bool)


def lutB(init, pins):
    live = [i for i, p in enumerate(pins) if not _isconst(p)]
    terms = []
    for bits in itertools.product((False, True), repeat=len(live)):
        idx = 0
        val = dict(zip(live, bits))
        for i, p in enumerate(pins):
            b = val[i] if i in val else p
            if b:
                idx |= 1 << i
        if (init >> idx) & 1:
            lits = [pins[i] if val[i] else z3.Not(pins[i]) for i in live]
            terms.append(z3.And(lits) if lits else z3.BoolVal(True))
    if not terms:
        return z3.BoolVal(False)
    return z3.Or(terms) if len(terms) > 1 else terms[0]


def o5(init):
    return init & 0xFFFFFFFF


def lutK(init, pins):
    """pins: ternary pairs (x, v).  Returns (x, v)."""
    n = len(pins)
    one, zero = [], []
    for idx in range(1 << n):
        cons = []
        ok = True
        for i, (px, pv) in enumerate(pins):
            b = bool((idx >> i) & 1)
            if _isconst(px) and _isconst(pv):
                if not px and pv != b:
                    ok = False
                    break
                continue
            cons.append(z3.Or(px, pv == b))
        if not ok:
            continue
        c = z3.And(cons) if cons else z3.BoolVal(True)
        (one if (init >> idx) & 1 else zero).append(c)
    # out is 1 iff no consistent 0-entry; 0 iff no consistent 1-entry
    is1 = z3.Not(z3.Or(zero)) if zero else z3.BoolVal(True)
    is0 = z3.Not(z3.Or(one)) if one else z3.BoolVal(True)
    return (z3.And(z3.Not(is1), z3.Not(is0)), is1)


def kval(S, n):
    return (S[n + '.x'], S[n + '.v'])


def kvar(ts, n):
    ts.bool(n + '.x')
    ts.bool(n + '.v')
    ts.init(lambda S: z3.Implies(S[n + '.x'], z3.Not(S[n + '.v'])))
    ts.trans(lambda S, N: z3.Implies(N[n + '.x'], z3.Not(N[n + '.v'])))
    return n


def keq(a, b):
    return z3.And(a[0] == b[0], a[1] == b[1])


def kjoin(vals):
    v0 = vals[0]
    allx = z3.Or([v[0] for v in vals])
    same = z3.And([v[1] == v0[1] for v in vals[1:]]) if len(vals) > 1 else z3.BoolVal(True)
    x = z3.Or(allx, z3.Not(same))
    return (x, z3.And(z3.Not(x), v0[1]))


def kof(b):
    return (z3.BoolVal(False), b)


def kfmt(r, n):
    return 'X' if r[n + '.x'] else ('1' if r[n + '.v'] else '_')


# -- binary channels ------------------------------------------------------

def win(ts, y, xf, lo, hi, fifo=False):
    """Output state var y.  Hist y~1..y~(hi-1) hold x(t-1)..x(t-hi+1)."""
    assert 1 <= lo <= hi
    ts.bool(y)
    hs = [ts.bool('%s~%d' % (y, j)) for j in range(1, hi)]

    def cand(S, d):          # x(t+1-d) as seen from tick t
        return xf(S) if d == 1 else S[hs[d - 2]]

    def tr(S, N):
        cs = []
        if hs:
            cs.append(N[hs[0]] == xf(S))
            for j in range(1, len(hs)):
                cs.append(N[hs[j]] == S[hs[j - 1]])
        if not fifo:
            cs.append(z3.Or([N[y] == cand(S, d) for d in range(lo, hi + 1)]))
        else:
            cs.append(z3.And([z3.Implies(N[y + '#d'] == d, N[y] == cand(S, d))
                              for d in range(lo, hi + 1)]))
            cs.append(N[y + '#d'] <= S[y + '#d'] + 1)
        return z3.And(cs)
    if fifo:
        ts.int(y + '#d', lo, hi)
    ts.trans(tr)
    return y


def inert(ts, y, xf, rise, fall):
    rlo, rhi = rise
    flo, fhi = fall
    assert 1 <= rlo <= rhi and 1 <= flo <= fhi
    ts.bool(y)
    c = ts.int(y + '#c', 0, max(rhi, fhi))
    ts.init(lambda S: S[c] == 0)

    def tr(S, N):
        x = xf(S)
        cnt = S[c] + 1
        lo = z3.If(x, rlo, flo)
        hi = z3.If(x, rhi, fhi)
        moved = N[y] != S[y]
        return z3.If(x == S[y],
                     z3.And(N[y] == S[y], N[c] == 0),
                     z3.And(z3.Implies(moved, z3.And(N[y] == x, cnt >= lo, N[c] == 0)),
                            z3.Implies(z3.Not(moved), z3.And(cnt < hi, N[c] == cnt))))
    ts.trans(tr)
    return y


def chan(ts, kind, y, xf, lo, hi, rf=None):
    if kind == 'win':
        return win(ts, y, xf, lo, hi)
    if kind == 'fifo':
        return win(ts, y, xf, lo, hi, fifo=True)
    if kind == 'inert':
        r = rf or ((lo, hi), (lo, hi))
        return inert(ts, y, xf, r[0], r[1])
    raise ValueError(kind)


# -- ternary channel ------------------------------------------------------

def kwin(ts, y, xf, lo, hi):
    """Ternary window channel; y and hist are ternary pairs."""
    assert 1 <= lo <= hi
    kvar(ts, y)
    hs = ['%s~%d' % (y, j) for j in range(1, hi)]
    for h in hs:
        kvar(ts, h)

    def cand(S, d):
        return xf(S) if d == 1 else kval(S, hs[d - 2])

    def tr(S, N):
        cs = []
        if hs:
            cs.append(keq(kval(N, hs[0]), xf(S)))
            for j in range(1, len(hs)):
                cs.append(keq(kval(N, hs[j]), kval(S, hs[j - 1])))
        cs.append(keq(kval(N, y), kjoin([cand(S, d) for d in range(lo, hi + 1)])))
        return z3.And(cs)
    ts.trans(tr)
    return y
