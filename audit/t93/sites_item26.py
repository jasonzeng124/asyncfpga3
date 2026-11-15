#!/usr/bin/env python3
"""T112b (audit): sites_gen.run_design on BOARD-QUEUE item 26 (c64eq seed 25, own build /root/t65/c64eq_25) at worst /
FAST_MIN / SLOW_MAX; full-carry static (no vector-range restriction). Writes sites_collatz64_item26.txt only."""
import sys, os, json, collections
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
import sites_gen as S
S.DESIGNS['G'] = dict(item=26, rj='/root/t65/c64eq_25/collatz64_bench_gen_routed.json', rtl='/root/t65/c64eq_25/collatz64_kernel_bench.v',
                      research=None,
                      work={'worst': '/root/t65/work_c64eq_25_mon1_worst', 'FAST_MIN': '/root/t65/work_c64eq_25_mon1_fastmin',
                            'SLOW_MAX': '/root/t65/work_c64eq_25_mon1_slowmax'},
                      corners=('worst', 'FAST_MIN', 'SLOW_MAX'), counter=None)
rows, notes = S.run_design('G', 2)
mn = collections.defaultdict(lambda: [None, None, None])
err = 0
for r in rows:
    if 'own' not in r: err += 1; continue
    k = (r['gate'], r['corner'])
    if mn[k][0] is None or r['own'] < mn[k][0]: mn[k] = [r['own'], r.get('orjoin'), r['launch'] + ('' if not r['transparent'] else ' T=' + ','.join(r['transparent']))]
L = ['T113b sites_item26.py -- own rule E (C-elements wait for their last input; full static carry) on item 26 (c64eq seed 25, sdf 6982a9d5)',
     f'rows {len(rows)}, rows without a result {err}', 'gate  corner  min_own_ps  orjoin_at_that_row  binding_launch']
for (g, c), (o, oj, l) in sorted(mn.items()):
    L.append(f'{g:24s} {c:9s} {o:7d} {str(oj):>7s}  {l}')
neg = [(k, v[0]) for k, v in mn.items() if v[0] < 0]
L.append(f'overall min own: {min(v[0] for v in mn.values())}; negative gates: {neg}')
L += ['notes:'] + notes[:60]
open(os.path.join(H, 'sites_collatz64_item26.txt'), 'w').write('\n'.join(L) + '\n')
json.dump(rows, open(os.path.join(H, 'sites_collatz64_item26.json'), 'w'), default=str)
print('\n'.join(L[:3] + [l for l in L if l.startswith('overall')]))
