#!/usr/bin/env python3
"""rsim.py DIR [N] -- differential random-schedule run of the imported rule lists DIR/A.lean and DIR/B.lean (fuse_check
--keep dir): Lean Rule.fire semantics (GcdHwLib), one token per input channel (random value within its declared width;
control inputs 0), random firing order to a terminal store; compares the token lists on the data output channel
(chOut) and on every input-free channel... only chOut is compared. Untrusted evidence, not a proof."""
import json, os, random, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
RS = os.environ.get('RS', '/tmp/claude-0/rs')   # a research checkout


def M(w): return (1 << w) - 1
def flip(w, a): return (a % (1 << w) + (1 << (w - 1))) % (1 << w)
def binop(o, w, a, b):
    k = o[0]; m = 1 << w
    if k == 'addi': return (a + b) % m
    if k == 'subi': return (a + m * (1 + b // m) - b) % m if False else (a - b) % m
    if k == 'muli': return (a * b) % m
    if k == 'andi': return (a & b) % m
    if k == 'ori': return (a | b) % m
    if k == 'xori': return (a ^ b) % m
    if k == 'shli': return (a << b) % m if b < 4096 else 0
    if k == 'shrui': return (a % m) >> b
    if k == 'shrsi':
        x = a % m
        return x >> b if x < (1 << (w - 1)) else (m - 1) - ((m - 1 - x) >> b)
    if k == 'cmpi':
        p = o[1][0]; x, y = a % m, b % m; sx, sy = flip(w, a), flip(w, b)
        return int({'eq': x == y, 'ne': x != y, 'ult': x < y, 'ule': x <= y, 'ugt': y < x, 'uge': y <= x,
                    'slt': sx < sy, 'sle': sx <= sy, 'sgt': sy < sx, 'sge': sy <= sx}[p])
    raise ValueError(o)

def ev(e, env):
    k = e[0]
    if k == 'var': return env[e[1]] if e[1] < len(env) else 0
    if k == 'lit': return e[1]
    if k == 'un':
        o, w, a = e[1], e[2], ev(e[3], env)
        if o[0] in ('trunci', 'extui'): return a % (1 << w)
        if o[0] == 'extsi':
            dw = o[1]; x = a % (1 << w)
            return x if x < (1 << (w - 1)) else x + (1 << dw) - (1 << w)
        raise ValueError(o)
    if k == 'bin': return binop(e[1], e[2], ev(e[3], env), ev(e[4], env))
    if k == 'sel': return ev(e[2], env) if ev(e[1], env) % 2 == 1 else ev(e[3], env)
    raise ValueError(e)

def norm(r):
    """rules_iso tuples -> (kind, ...) with E in fuse_check's tuple form."""
    return r

def fire(r, st):
    k = r[0]
    if k == 'mux':
        s, ds, o, iw = r[1], r[2], r[3], r[4]
        if not st.get(s): return False
        j = st[s][0] % (1 << iw)
        if j >= len(ds): return False
        d = ds[j]
        if d == s or not st.get(d): return False
        st[s].pop(0); x = st[d].pop(0); st.setdefault(o, []).append(x); return True
    ins = {'comp': lambda: r[1], 'fork': lambda: [r[1]], 'branch': lambda: [r[1], r[2]], 'cm': lambda: [r[1]],
           'sink': lambda: [r[1]]}[k]()
    if not all(st.get(c) for c in ins): return False
    vs = [st[c][0] for c in ins]
    for c in ins: st[c].pop(0)
    if k == 'comp': st.setdefault(r[2], []).append(ev(r[3], vs))
    elif k == 'fork':
        for o in r[2]: st.setdefault(o, []).append(vs[0])
    elif k == 'branch': st.setdefault(r[3] if vs[0] % 2 == 1 else r[4], []).append(vs[1])
    elif k == 'cm': st.setdefault(r[2], []).append(vs[0]); st.setdefault(r[3], []).append(r[4])
    return True

def run(R, init, rng, limit=60000):
    st = {c: list(v) for c, v in init.items()}; n = 0
    while n < limit:
        order = list(range(len(R))); rng.shuffle(order); hit = False
        for l in order:
            if fire(R[l], st): hit = True; n += 1; break
        if not hit: return st, True
    return st, False

def main():
    k = sys.argv[1]; n = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    ea = sys.argv[3] if len(sys.argv) > 3 else 'BDC_AUTO=1,BDC_RING_FUSE=0'
    eb = sys.argv[4] if len(sys.argv) > 4 else 'BDC_AUTO=1,BDC_SIBLING_FUSE=1'
    import fuse_check as FC
    FC.PP.BDCDIR = RS + '/bdc'
    F = RS + '/cloud/fixtures/frontend/%s/comp/handshake_transformed.mlir' % k
    import tempfile; tmp = tempfile.mkdtemp(prefix='rsim_' + k + '_'); os.makedirs(tmp, exist_ok=True)
    Ra, _, oa, na = FC.imp(F, tmp + '/A.lean', 'FuA', FC.parse_env(ea))
    Rb, _, ob, nb = FC.imp(F, tmp + '/B.lean', 'FuB', FC.parse_env(eb))
    if len(sys.argv) > 5: Rb = FC.mutate(Rb, sys.argv[5])
    wi = FC.input_widths(tmp + '/A.lean.widths.json', na)
    rng = random.Random(1); bad = 0; done = 0
    for v in range(n):
        init = {}
        for c in range(na):
            w = wi[c]
            if w == 0: init[c] = [0]
            else:
                r = rng.random()
                x = rng.choice([0, 1, 2, 3, 5, 7, 10, M(w)]) if r < 0.6 else rng.randrange(1 << min(w, 6)) if r < 0.85 else rng.randrange(1 << w)
                init[c] = [x]
        outs = set()
        for s in range(4):
            for R, o in ((Ra, oa), (Rb, ob)):
                st, q = run(R, init, random.Random(1000 * v + s))
                outs.add(('q' if q else 'LIMIT', tuple(st.get(o, []))))
        done += 1
        if len(outs) != 1: bad += 1; print('DIFF', k, init, outs)
    print('%s: %d vectors x 4 schedules x {A,B}: %s' % (k, done, 'all agree on chOut' if not bad else '%d DIFFER' % bad), sorted(outs)[:1])

if __name__ == '__main__':
    main()
