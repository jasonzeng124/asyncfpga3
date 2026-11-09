"""print the A-side (start) of the U' claims of a latch's H->U' truncations, recursively through covers (light, no ao)"""
import sys, pickle
sys.path.insert(0, '.')
from classify import load
C = load(); nm = C['names']; idx = {n: i for i, n in enumerate(nm)}; EX = C['EXACT']; g = C['gates']
c = int(sys.argv[2]); H = pickle.load(open('hist_c%d.pkl' % c, 'rb')); R = H['R']; t0 = R - 1; hist = H['hist']
el = []
for n in sorted(EX):
    for k, t in enumerate([x for x in (hist[n][1] if n in hist else []) if x > t0]): el.append((n, k, t))
def E(e): return None if e is None else "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
P = pickle.load(open(sys.argv[1], 'rb')); M = P['MEMO']
def show(key, d, maxd):
    cl = M.get(key)
    if cl is None: print('  ' * d, '?', nm[key[0]]); return
    print('  ' * d, nm[key[0]], cl.get('kind'), 'A', E(cl.get('A')), 'a', cl.get('a'), 'B', E(cl.get('B')), 'b', cl.get('b'), 'ph', [(p[0]) for p in cl.get('phases') or []])
    if d < maxd:
        seen = set()
        for u, k in (cl.get('cov') or []):
            if k is not None and k not in seen: seen.add(k); show(k, d + 1, maxd)
done = set()
for tr in P['TRUNC']:
    if nm[tr['Q']] != sys.argv[3] or tr['kind'] != "H->U'": continue
    c2 = tr['c2']
    if (c2['A'], c2['a']) in done: continue
    done.add((c2['A'], c2['a']))
    print("U' A", E(c2['A']), 'a', c2['a'], "| H ends", E(tr['c1']['B']), 'b', tr['c1']['b'], 'margin', tr['margin'])
    for (u, k, B, b) in c2.get('pins', []):
        show(k, 1, int(sys.argv[4]))
