#!/usr/bin/env python3
"""C-8x2: classify the 465 channels of CapstoneNet for the relaxed (busy-gated) model.
Reads formal/lean/Formal/Net/CapstoneNet.lean (ops list) and
formal/tools/oblgen/out/obligations.tsv (tcheck expectation per channel).
Writes Wip/C8x2/classes.tsv and prints a summary + a Lean rank table."""
import re, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))   # formal/
src = open(os.path.join(ROOT, 'lean/Formal/Net/CapstoneNet.lean')).read()
body = src[src.index('def ops : List (K NC) := ['):]
lines = [l.strip().rstrip(',') for l in body.splitlines()[1:]]
ops = []
for l in lines:
    if l.startswith(']'): break
    if l.startswith('K.'): ops.append(l)
def ints(s): return [int(x) for x in re.findall(r'\d+', s)]
def parse(l):
    kind = l.split()[0][2:]
    if kind == 'forkG':
        m = re.match(r'K\.forkG (\d+) \[([^\]]*)\]', l); i = int(m[1]); os_ = ints(m[2]); return kind, [i], os_
    if kind == 'forkH':
        m = re.match(r'K\.forkH (\d+) \[(.*?)\] ', l); i = int(m[1])
        os_ = [int(a) for a, _ in re.findall(r'\((\d+), (\d+)\)', m[2])]; return kind, [i], os_
    if kind == 'join':
        m = re.match(r'K\.join \[([^\]]*)\] (\d+)', l); return kind, ints(m[1]), [int(m[2])]
    if kind == 'bjoin':
        m = re.match(r'K\.bjoin \[([^\]]*)\] (\d+)', l); return kind, ints(m[1]), [int(m[2])]
    if kind in ('steerC', 'steerD'):
        m = re.match(r'K\.\w+ (\d+) (\d+) (\d+)', l); return kind, [int(m[1])], [int(m[2]), int(m[3])]
    if kind == 'mux':
        m = re.match(r'K\.mux (\d+) (\d+) (\d+) (\d+)', l); return kind, [int(m[1]), int(m[2]), int(m[3])], [int(m[4])]
    if kind == 'muxn':
        m = re.match(r'K\.muxn (\d+) (\d+) (\d+) (\d+) (\d+)', l); return kind, ints(' '.join(m.groups()[:4])), [int(m[5])]
    if kind == 'amerge':
        m = re.match(r'K\.amerge (\d+) (\d+) (\d+)', l); return kind, [int(m[1]), int(m[2])], [int(m[3])]
    if kind == 'link':
        m = re.match(r'K\.link (\d+) (\d+)', l); return kind, [int(m[1])], [int(m[2])]
    if kind == 'src':
        m = re.match(r'K\.src (\d+)', l); return kind, [], [int(m[1])]
    if kind == 'sink':
        m = re.match(r'K\.sink (\d+)', l); return kind, [int(m[1])], []
    raise ValueError(l)
P = [parse(l) for l in ops]
assert len(P) == 367, len(P)
NC = 465
prod = {}; cons = {}
for o, (k, i, out) in enumerate(P):
    for c in out: prod[c] = o
    for c in i: cons[c] = o
assert len(prod) == NC and len(cons) == NC
# disjointness
bad = [o for o, (k, i, out) in enumerate(P) if set(i) & set(out)]
STRUCT = {'forkG', 'forkH', 'join', 'bjoin', 'steerC', 'steerD', 'link', 'src'}
root = [c for c in range(NC) if P[prod[c]][0] not in STRUCT]
# rank: structural channel c depends on all inputs of prod c
rank = {}
sys.setrecursionlimit(10000)
state = {}
def rk(c):
    if c in rank: return rank[c]
    if state.get(c) == 1: raise RuntimeError('cycle through %d' % c)
    state[c] = 1
    k, ins, _ = P[prod[c]]
    r = 0 if k not in STRUCT else 1 + max([rk(i) for i in ins], default=-1)
    rank[c] = r; state[c] = 2; return r
for c in range(NC): rk(c)
# obligations.tsv
obl = {}
for l in open(os.path.join(ROOT, 'tools/oblgen/out/obligations.tsv')):
    f = l.rstrip('\n').split('\t')
    if f[1].startswith('H_BUNDLE('):
        c = int(re.match(r'chan (\d+)', f[2])[1]); obl[c] = (f[3], f[4])
CAPT = {'link', 'steerC', 'steerD', 'mux', 'muxn', 'sink'}
# per-operator obligations (I rows per link stage, E rows per steer/mux select)
opobl = {}
for l in open(os.path.join(ROOT, 'tools/oblgen/out/obligations.tsv')):
    f = l.rstrip('\n').split('\t')
    m = re.match(r'op (\d+)', f[2]) if len(f) > 2 else None
    if m: opobl.setdefault(int(m[1]), []).append((f[1].split('(')[0], f[4]))
def need_row(c):
    pk = P[prod[c]][0]; co = cons[c]; ck = P[co][0]
    if c in root:
        return 'BCert root: ' + ('A row (exists)' if obl[c][1] == 'A' else 'NEW ROW NEEDED (no tcheck row)')
    if ck == 'link':
        kinds = [e for (n_, e) in opobl.get(co, []) if n_ == 'Sep+SetupHold']
        if any(e.startswith('vacuous') for e in kinds): return 'ghost (W=0 control stage: no data pins)'
        if any(e == 'I' for e in kinds): return 'field backed by I/H row of the stage (exists)'
        return 'latch-D, NO ROW FOUND'
    if ck in ('steerC', 'steerD'):
        kinds = [e for (n_, e) in opobl.get(co, []) if n_ == 'H_STEER_SEL']
        return 'field backed by E row of the steer select (exists)' if kinds else 'steer select, NO ROW FOUND'
    if ck == 'mux' and P[co][1][0] == c:
        kinds = [e for (n_, e) in opobl.get(co, []) if n_ == 'H_MUX_SEL']
        return 'field backed by E row of the mux select (exists)' if kinds else 'mux select, NO ROW FOUND'
    if ck == 'muxn' and P[co][1][0] == c:
        return 'NEW ROW NEEDED (muxn select: no E row on any route)'
    return 'ghost (consumer does not sample the bus)'
with open(os.path.join(HERE, 'classes.tsv'), 'w') as w:
    w.write('chan\tprod\tcons\tinstance\t8w_expect\theld_class\trank\tcapture\trow_need\n')
    for c in range(NC):
        pk = P[prod[c]][0]; ck = P[cons[c]][0]
        hc = 'BCERT' if c in root else 'structural:' + {'forkG':'forkB_held','forkH':'forkB_held','join':'joinB_held','bjoin':'joinB_held','steerC':'steerB_held','steerD':'steerB_held','link':'linkB_held','src':'srcB_held'}[pk]
        # what the consumer does with the bus
        if ck == 'link': cap = 'latch-D (rows I/H)'
        elif ck in ('steerC', 'steerD'): cap = 'steer select LUT (row E)'
        elif ck == 'mux': cap = ('mux select LUT (row E)' if P[cons[c]][1][0] == c else 'comb (mux data)')
        elif ck == 'muxn': cap = ('muxn select LUT (NO row)' if P[cons[c]][1][0] == c else 'comb (mux data)')
        elif ck == 'sink': cap = 'environment'
        else: cap = 'comb (' + ck + ')'
        inst, exp = obl.get(c, ('?', '?'))
        w.write(f'{c}\t{pk}\t{ck}\t{inst}\t{exp}\t{hc}\t{rank[c]}\t{cap}\t{need_row(c)}\n')
from collections import Counter
print('disjointness violations:', bad)
print('BCERT roots:', len(root), Counter(P[prod[c]][0] for c in root))
print('roots by 8w expectation:', Counter(obl[c][1] for c in root))
print('roots without an A row:', [(c, obl[c]) for c in root if obl[c][1] != 'A'])
print('max rank:', max(rank.values()))
print('structural by producer:', Counter(P[prod[c]][0] for c in range(NC) if c not in root))
print('8w derived/ghost (376) now structural:', sum(1 for c in range(NC) if c not in root and (obl[c][1].startswith('derived') or obl[c][1].startswith('ghost'))))
print('8w A-class now structural:', [c for c in range(NC) if c not in root and obl[c][1]=='A'])
print('capture kinds:', Counter(l.split('\t')[7].strip() for l in open(os.path.join(HERE,'classes.tsv')).readlines()[1:]))
print('row need:'); [print('  %4d  %s' % (v, k)) for k, v in Counter(need_row(c) for c in range(NC)).most_common()]
print('NEW ROWS:', [(c, obl[c][0], need_row(c)) for c in range(NC) if 'NEW' in need_row(c) or 'NO ROW' in need_row(c)])
if '--lean' in sys.argv:
    print('rootL:', [1 if c in root else 0 for c in range(NC)])
    print('rankL:', [rank[c] for c in range(NC)])
