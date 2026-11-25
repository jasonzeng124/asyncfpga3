#!/usr/bin/env python3
"""Simulation (NOT a proof) of Formal/Net/KahnGcdCM.lean's graph G2 with TWO
invocations in flight (two start tokens), i.e. H_ONE_INVOCATION violated.
Random schedules; prints the set of distinct terminal `out` FIFOs.
Also runs the textbook-mux graph G (KahnGcd.lean) with two invocations for contrast.
    python3 -I formal/lean/Wip/C8b/sim_two_invocations.py
"""
import random

def strip2(n):
    while n > 0 and n % 2 == 0:
        n //= 2
    return n

def absdiff(a, b):
    return a - b if b <= a else b - a

tst = lambda v: v != 0

def strict(ins, f):
    def fire(s):
        if all(s[c] for c in ins):
            vs = [s[c][0] for c in ins]
            return {c: 1 for c in ins}, f(vs)
        return None
    return fire

def op1(a, o, g): return strict([a], lambda vs: {o: [g(vs[0])]})
def op2(a, b, o, g): return strict([a, b], lambda vs: {o: [g(vs[0], vs[1])]})
def fork(a, os): return strict([a], lambda vs: {o: [vs[0]] for o in os})
def branch(c, d, oT, oF): return strict([c, d], lambda vs: {(oT if tst(vs[0]) else oF): [vs[1]]})
def sink(a): return strict([a], lambda vs: {})
def mux(c, d0, d1, o):
    def fire(s):
        if not s[c]:
            return None
        d = d1 if tst(s[c][0]) else d0
        if not s[d]:
            return None
        return {c: 1, d: 1}, {o: [s[d][0]]}
    return fire

body = dict(
    muxA=mux('sA', 'inA', 'backA', 'hA'), muxB=mux('sB', 'inB', 'backB', 'hB'),
    forkA=fork('hA', ['hA1', 'hA2']), isnz=op1('hA1', 'cnd', lambda x: 0 if x == 0 else 1),
    brA=branch('cA', 'hA2', 'aT', 'aF'), brB=branch('cB', 'hB', 'bT', 'out'),
    snkA=sink('aF'), forkAT=fork('aT', ['a1', 'a2']), forkBT=fork('bT', ['b1', 'b2']),
    sub=op2('a1', 'b1', 'backA', lambda x, y: strip2(absdiff(x, y))),
    mn=op2('a2', 'b2', 'backB', min))

G2 = dict(body, cmL=strict(['start'], lambda vs: {'hC': [vs[0]], 'idx': [0]}),
          cmR=strict(['backC'], lambda vs: {'hC': [vs[0]], 'idx': [1]}),
          forkI=fork('idx', ['sA', 'sB']), forkC=fork('cnd', ['cA', 'cB', 'cC']),
          brC=branch('cC', 'hC', 'backC', 'exitC'))
G = dict(body, forkC=fork('cnd', ['cA', 'cB', 'sA', 'sB']))

def run(G, init, rng):
    s = {}
    for f in G.values():
        pass
    from collections import defaultdict
    s = defaultdict(list, {k: list(v) for k, v in init.items()})
    while True:
        en = [(l, r) for l, f in G.items() if (r := f(s)) is not None]
        if not en:
            return tuple(s['out'])
        l, (k, p) = rng.choice(en)
        for c, n in k.items():
            s[c] = s[c][n:]
        for c, v in p.items():
            s[c] = s[c] + v

if __name__ == '__main__':
    rng = random.Random(1)
    (a1, b1), (a2, b2) = (3, 5), (0, 7)   # loop-entry pairs: b odd, a odd or 0
    init2 = dict(start=[0, 0], inA=[a1, a2], inB=[b1, b2])
    init1 = dict(sA=[0], sB=[0], inA=[a1, a2], inB=[b1, b2])
    print('G2 (control_merge), two invocations:',
          sorted({run(G2, init2, rng) for _ in range(2000)}))
    print('G  (primed mux),    two invocations:',
          sorted({run(G, init1, rng) for _ in range(2000)}))
    print('expected per invocation (C loop):', 1, 7)

def run_pri(G, init, avoid):
    """Deterministic schedule that fires labels in `avoid` only when nothing else is enabled."""
    from collections import defaultdict
    s = defaultdict(list, {k: list(v) for k, v in init.items()})
    while True:
        en = [(l, r) for l, f in G.items() if (r := f(s)) is not None]
        if not en:
            return tuple(s['out'])
        pref = [e for e in en if e[0] not in avoid] or en
        l, (k, p) = pref[0]
        for c, n in k.items():
            s[c] = s[c][n:]
        for c, v in p.items():
            s[c] = s[c] + v

if __name__ == '__main__':
    init2 = dict(start=[0, 0], inA=[3, 0], inB=[5, 7])
    print('G2, cmL starved (first invocation runs alone first):', run_pri(G2, init2, {'cmL'}))
    print('G2, cmL eager:', run_pri(G2, init2, {'cmR'}))
    bad = 0
    for a1 in [0, 1, 3, 5, 7, 9, 15]:
        for b1 in [1, 3, 5, 9, 21]:
            for a2 in [0, 1, 3, 25]:
                for b2 in [1, 7, 15]:
                    init = dict(start=[0, 0], inA=[a1, a2], inB=[b1, b2])
                    outs = {run(G2, init, rng) for _ in range(30)} | \
                           {run_pri(G2, init, {'cmL'}), run_pri(G2, init, {'cmR'})}
                    import math
                    for o in outs:
                        if sorted(o) != sorted([math.gcd(a1, b1), math.gcd(a2, b2)]):
                            bad += 1
                            if bad < 5: print('WRONG VALUES', (a1, b1, a2, b2), o)
    print('value-corrupting outcomes found:', bad)
