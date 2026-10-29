# P9 audit: for every exactness=="exact" row, check named role=="exact" Lean theorems exist
# in the named file and that their statement contains an iff.
import json, re, sys, collections
root = sys.argv[1]  # ~/wt-f9 (contains formal/)
d = json.load(open(root + '/formal/out/cell_constraints.json'))
C = d['constraints']
print('rows', len(C), collections.Counter(r.get('exactness') for r in C))
def stmt(path, name):
    try: src = open(root + '/' + path).read()
    except FileNotFoundError: return None, 'NOFILE'
    short = name.split('.')[-1]
    m = re.search(r'^(?:private )?(?:theorem|lemma)\s+' + re.escape(short) + r'\b(.*?)(:=)', src, re.S | re.M)
    if not m: return None, 'NOTHM'
    return m.group(1), 'ok'
bad = []; n = 0
for r in C:
    if r.get('exactness') != 'exact': continue
    n += 1
    ex = [l for l in r['lean'] if l.get('role') == 'exact']
    if not ex: bad.append((r['id'], 'no lean role=exact')); continue
    oks = []
    for l in ex:
        s, st = stmt(l['file'], l['name'])
        iff = s is not None and ('↔' in s)
        oks.append((l['name'], st, iff))
    if not any(st == 'ok' and iff for _, st, iff in oks):
        bad.append((r['id'], oks))
    print(r['id'], '|', r.get('strict'), '|', [(a, b, c) for a, b, c in oks])
print('exact rows', n); print('BAD', len(bad))
for b in bad: print('  BAD', b)
