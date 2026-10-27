#!/usr/bin/env python3
"""Synchronous unit-delay run of 8f's gcd network (OpsGcd.net) with the
2-place initial-token buffers and one-shot sources.  Every gate moves to its
function of the previous tick (a legal instance of the SI/DI models: unbounded
inertial delay, here exactly 1).  Prints the trace length, the out handshake
and, with -lean, the Lean table for Formal/Net/OpsWitness.lean.
It proves nothing; Lean re-checks every step of the table."""
import sys

GC = "inA inB sA sB backA backB hA hB hA1 hA2 cnd cA cB sA' sB' jA jB aT aF bT out a1 a2 b1 b2".split()
I = {c: i for i, c in enumerate(GC)}

def strip2(x):
    if x == 0: return 0
    while x % 2 == 0: x //= 2
    return x

def run(a, b, cap=2, T=400):
    R = {c: False for c in GC}; K = {c: False for c in GC}
    D = {c: 0 for c in GC}
    J = dict(j0A=False, j1A=False, j0B=False, j1B=False)
    env = dict(sentA=False, sentB=False, cntA=1, cntB=1, qA=[0], qB=[0], valA=0, valB=0)
    hist = []
    def C(a_, b_, q): return a_ if a_ == b_ else q
    def data():
        D['inA'] = a; D['inB'] = b
        D['sA'] = env['valA']; D['sB'] = env['valB']
        # loop data: back* from previous tick (sim only)
        D['hA'] = D['backA'] if D['sA'] != 0 else D['inA']
        D['hB'] = D['backB'] if D['sB'] != 0 else D['inB']
        D['hA1'] = D['hA2'] = D['hA']
        D['cnd'] = 0 if D['hA1'] == 0 else 1
        for c in ['cA', 'cB', "sA'", "sB'"]: D[c] = D['cnd']
        D['jA'] = 2 * D['hA2'] + (0 if D['cA'] == 0 else 1)
        D['jB'] = 2 * D['hB'] + (0 if D['cB'] == 0 else 1)
        D['aT'] = D['aF'] = D['jA'] // 2; D['bT'] = D['out'] = D['jB'] // 2
        D['a1'] = D['a2'] = D['aT']; D['b1'] = D['b2'] = D['bT']
        D['backA'] = strip2(abs(D['a1'] - D['b1'])); D['backB'] = min(D['a2'], D['b2'])
    for _ in range(3): data()
    for t in range(T):
        hist.append((dict(R), dict(K), dict(J), dict(D)))
        nR, nK, nJ = dict(R), dict(K), dict(J)
        sel = lambda c: D[c] % 2 == 1
        tst = lambda c: D[c] != 0
        # muxes
        for (x, y, c, z, j0, j1) in [('inA', 'backA', 'sA', 'hA', 'j0A', 'j1A'),
                                     ('inB', 'backB', 'sB', 'hB', 'j0B', 'j1B')]:
            s = tst(c)
            nJ[j0] = C(R[x], R[c] and not s, J[j0]); nJ[j1] = C(R[y], R[c] and s, J[j1])
            nR[z] = J[j0] or J[j1]
            nK[x] = C(J[j0], K[z], K[x]); nK[y] = C(J[j1], K[z], K[y]); nK[c] = K[z]
        def fork(a_, os):
            for o in os: nR[o] = R[a_]
            v = K[os[0]]
            if all(K[o] == v for o in os): nK[a_] = v
        def join(is_, o):
            v = R[is_[0]]
            if all(R[i] == v for i in is_): nR[o] = v
            for i in is_: nK[i] = K[o]
        def steer(j, oT, oF):
            s = sel(j)
            nR[oT] = R[j] and s; nR[oF] = R[j] and not s
            nK[j] = K[oT] or K[oF]
        fork('hA', ['hA1', 'hA2']); join(['hA1'], 'cnd'); fork('cnd', ['cA', 'cB', "sA'", "sB'"])
        join(['cA', 'hA2'], 'jA'); steer('jA', 'aT', 'aF'); join(['cB', 'hB'], 'jB')
        steer('jB', 'bT', 'out'); nK['aF'] = R['aF']; fork('aT', ['a1', 'a2']); fork('bT', ['b1', 'b2'])
        join(['a1', 'b1'], 'backA'); join(['a2', 'b2'], 'backB')
        nK['out'] = R['out']
        # sources: one token each
        for c, f in [('inA', 'sentA'), ('inB', 'sentB')]:
            nR[c] = False if (K[c] or env[f]) else True
            if K[c]: env[f] = True
        # initial-token buffers, capacity `cap`
        for i, o, q, v in [("sA'", 'sA', 'qA', 'valA'), ("sB'", 'sB', 'qB', 'valB')]:
            Q = env[q]
            if R[i] and not K[i] and len(Q) < cap:
                nK[i] = True; Q.append(D[i])
            elif not R[i] and K[i]:
                nK[i] = False
            if not R[o] and not K[o] and Q and not env.get(o + 'busy'):
                nR[o] = True; env[v] = Q[0]; env[o + 'busy'] = True
            elif R[o] and K[o]:
                nR[o] = False; Q.pop(0); env[o + 'busy'] = False
        R, K, J = nR, nK, nJ
        data()
    return hist

def mask(d, keys):
    return sum(1 << i for i, k in enumerate(keys) if d[k])

if __name__ == '__main__':
    a = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1] != '-lean' else 0
    b = 1
    for cap in (1, 2):
        h = run(a, b, cap)
        outs = [t for t in range(len(h) - 1) if h[t][1]['out'] and not h[t + 1][1]['out']]
        last = max(t for t in range(1, len(h)) if h[t][:3] != h[t - 1][:3])
        print(f"a={a} b={b} cap={cap}: last change at t={last}, out ack falls at {outs}",
              file=sys.stderr)
    if '-lean' in sys.argv:
        h = run(0, 1, 2)
        last = max(t for t in range(1, len(h)) if h[t][:3] != h[t - 1][:3])
        rows = []
        for t in range(last + 1):
            R, K, J, _ = h[t]
            rows.append(f"⟨{mask(R, GC)}, {mask(K, GC)}, {mask(J, ['j0A','j1A','j0B','j1B'])}⟩")
        print("def tbl : List St := [\n  " + ",\n  ".join(rows[:-1]) + "]")
        print("def fin : St := " + rows[-1])
