import json, sys, lzma, hashlib
def load(p): return json.load(lzma.open(p, 'rt') if p.endswith('.xz') else open(p))
A, B = load(sys.argv[1]), load(sys.argv[2])
def canon(m):
    cells = m.get('cells', {})
    return hashlib.md5(json.dumps(sorted((n, c['type'], sorted(c.get('parameters', {}).items()), sorted((k, v) for k, v in c.get('connections', {}).items())) for n, c in cells.items()), sort_keys=True).encode()).hexdigest()
ma, mb = A['modules'], B['modules']
common = set(ma) & set(mb)
diff = [m for m in common if canon(ma[m]) != canon(mb[m])]
print('modules A', len(ma), 'B', len(mb), 'common', len(common), 'only A', len(set(ma)-set(mb)), 'only B', len(set(mb)-set(ma)), 'differing common', len(diff), diff[:5])
