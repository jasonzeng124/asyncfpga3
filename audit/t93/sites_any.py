#!/usr/bin/env python3
"""T126 (audit): own rule E (sites_gen.run_design, C-element joins, full static carry) on any own route, 3 corners.
usage: sites_any.py ROUTE KERNEL ITEM SDFMD5  (work dirs /root/t65/work_ROUTE_mon1_{worst,fastmin,slowmax}); writes
t93/sites_ROUTE.txt / .json"""
import sys, os, json, collections
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
import sites_gen as S
R, K, ITEM, MD5 = sys.argv[1:5]
S.DESIGNS['E'] = dict(item=int(ITEM), rj=f'/root/t65/{R}/{K}_bench_gen_routed.json', rtl=f'/root/t65/{R}/{K}_kernel_bench.v',
                      research=None,
                      work={'worst': f'/root/t65/work_{R}_mon1_worst', 'FAST_MIN': f'/root/t65/work_{R}_mon1_fastmin',
                            'SLOW_MAX': f'/root/t65/work_{R}_mon1_slowmax'},
                      corners=('worst', 'FAST_MIN', 'SLOW_MAX'), counter=None)
rows, notes = S.run_design('E', 2)
mn = collections.defaultdict(lambda: [None, None, None]); err = 0
for r in rows:
    if 'own' not in r: err += 1; continue
    k = (r['gate'], r['corner'])
    if mn[k][0] is None or r['own'] < mn[k][0]: mn[k] = [r['own'], r.get('orjoin'), r['launch'] + ('' if not r['transparent'] else ' T=' + ','.join(r['transparent']))]
L = [f'T126 sites_any.py -- own rule E (C-element joins; full static carry) on item {ITEM} ({R}, sdf {MD5})',
     f'rows {len(rows)}, rows without a result {err}', 'gate  corner  min_own_ps  orjoin_at_that_row  binding_launch']
for (g, c), (o, oj, l) in sorted(mn.items()):
    L.append(f'{g:24s} {c:9s} {o:7d} {str(oj):>7s}  {l}')
neg = [(k, v[0]) for k, v in mn.items() if v[0] < 0]
L.append(f'overall min own: {min(v[0] for v in mn.values())}; negative gates: {neg}')
L += ['notes:'] + notes[:60]
open(os.path.join(H, f'sites_{R}.txt'), 'w').write('\n'.join(L) + '\n')
json.dump(rows, open(os.path.join(H, f'sites_{R}.json'), 'w'), default=str)
print('\n'.join(L[:3] + [l for l in L if l.startswith('overall')]))
