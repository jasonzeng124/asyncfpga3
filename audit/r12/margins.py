#!/usr/bin/env python3
"""Summarise SLACK lines from probe runs. usage: margins.py log...
setup margin = minsu - TSU (only meaningful when TSU > 0; TSU <= 0 means the
model checks nothing on the setup side, and the hold check covers it);
hold margin = minhd - THD.  Sentinel 1e9 = never observed."""
import re, sys
S = 1000000000
best_su = best_hd = best_all = None; n = 0; never_su = never_hd = 0; viol = []
per = {}
for fn in sys.argv[1:]:
    for l in open(fn):
        m = re.match(r'SLACK (\S+) TSU=(-?\d+) THD=(-?\d+) nck=(\d+) nin=(\d+) minsu=(\d+) minhd=(\d+)', l)
        if not m:
            continue
        name, tsu, thd, nck, nin, su, hd = m.group(1), *map(int, m.groups()[1:])
        n += 1
        if su < S:
            if best_all is None or su - tsu < best_all[0]: best_all = (su - tsu, name, su, tsu, fn)
            if tsu > 0:
                mg = su - tsu
                if best_su is None or mg < best_su[0]: best_su = (mg, name, su, tsu, fn)
                if mg < 0: viol.append(('SU', name, su, tsu, fn))
        else:
            never_su += 1
        if hd < S:
            mg = hd - thd
            if best_hd is None or mg < best_hd[0]: best_hd = (mg, name, hd, thd, fn)
            if mg < 0: viol.append(('HD', name, hd, thd, fn))
        else:
            never_hd += 1
        p = per.setdefault(name, [S, S]); p[0] = min(p[0], su); p[1] = min(p[1], hd)
print(f'{n} SLACK lines, {len(per)} flops, {len(sys.argv)-1} logs')
print(f'tightest setup margin (TSU>0): {best_su}')
print(f'tightest setup margin incl. TSU<=0 flops (minsu - TSU): {best_all}')
print(f'tightest hold margin: {best_hd}')
print(f'flop-runs with no setup sample: {never_su}, no hold sample: {never_hd}')
print(f'flops never sampled on hold over all logs: {sum(1 for v in per.values() if v[1] >= S)}')
print(f'probe-measured violations: {len(viol)}')
for v in viol[:20]: print('  ', v)
