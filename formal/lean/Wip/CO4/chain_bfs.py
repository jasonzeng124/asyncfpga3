# CO4: brute-force the per-gate SI semantics of the bd_delay chain variants
# under END-ONLY persistence (input x0 flips only when the chain end equals it).
# Reports whether the end can move to a value != x0 (previous tick).
import itertools, sys
def variants(n):
    buf = lambda k: (lambda s: s[k-1])
    yield "sym", [buf(k) for k in range(1, n+1)]
    # FASTFALL: g0 = buf(a), gi = s[i] & a ; a = x0
    yield "fastfall", [buf(1)] + [(lambda k: (lambda s: s[k-1] and s[0]))(k) for k in range(2, n+1)]
    yield "fastrise", [buf(1)] + [(lambda k: (lambda s: s[k-1] or s[0]))(k) for k in range(2, n+1)]
    # gated with anchor: x1 = uor buf(gate=x0); x2 = buf(x1); xk = x(k-1) & x0
    if n >= 2:
        yield "gated+anchor", [buf(1), buf(2)] + [(lambda k: (lambda s: s[k-1] and s[0]))(k) for k in range(3, n+1)]
for n in range(1, 6):
    for name, G in variants(n):
        init = (False,)*(n+1)
        seen = {init}; todo = [init]; bad = None
        while todo and bad is None:
            s = todo.pop()
            exc = [k for k in range(1, n+1) if G[k-1](s) != s[k]]
            x0opts = [s[0], not s[0]] if s[n] == s[0] else [s[0]]
            for sub in itertools.chain.from_iterable(itertools.combinations(exc, r) for r in range(len(exc)+1)):
                for x0 in x0opts:
                    t = list(s); t[0] = x0
                    for k in sub: t[k] = not s[k]
                    t = tuple(t)
                    if t[n] != s[n] and t[n] != s[0]:
                        bad = (s, t); break
                    if t not in seen: seen.add(t); todo.append(t)
                if bad: break
        print(f"n={n} {name:13s} states={len(seen):3d} end-only persistence {'OK' if bad is None else 'HAZARD '+str(bad)}")
