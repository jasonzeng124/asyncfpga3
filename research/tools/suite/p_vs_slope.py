#!/usr/bin/env python3
# P (the event graph's period) against the bench's own per-iteration time: the least-squares slope of a route's call latencies
# on Dynamatic's header executions per call of the most executed loop (dynamatic_lat.tsv), per route, over every farm
# result under DIR (default /tmp/bot/farmres: one directory per request, results/<req>/<task>/ copied). Read-only.
# Usage: p_vs_slope.py [DIR]
import glob, os, re, statistics as st, sys
lat = {}
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../data/suite/dynamatic/dynamatic_lat.tsv')):
    if l.startswith('#'): continue
    c = l.rstrip('\n').split('\t')
    if len(c) < 11 or c[10] in ('-', ''): continue
    lat[c[0]] = (c[4], [int(x) for x in c[10].split(',')], c[9])
def slope(x, y):
    n = len(x); mx, my = sum(x)/n, sum(y)/n
    sxx = sum((a-mx)**2 for a in x)
    return None if sxx == 0 else sum((a-mx)*(b-my) for a, b in zip(x, y))/sxx
rows = {}
for rf in glob.glob(os.path.join(sys.argv[1] if len(sys.argv) > 1 else '/tmp/bot/farmres', '*/*/result.txt')):
    d = os.path.dirname(rf)
    t = open(rf).read().split('\n')[0]
    m = re.match(r'(\S+) (\d+) status=PASS .*?P=(\d+)', t)
    if not m: continue
    k, seed, P = m.group(1), m.group(2), int(m.group(3))
    if k not in lat: continue
    per = {}
    for f in glob.glob(d + '/benchres_*.txt'):
        for l in open(f):
            dd = dict(re.findall(r'(\w+)=(\S+)', l))
            if 'batch' in dd and 'latmin' in dd:
                per.setdefault(int(dd['batch']), []).append(int(dd['latmin'])*int(dd.get('fclk_ps', 12000))/1000.0)
    trips = lat[k][1]
    if len(per) != len(trips): continue
    y = [st.median(v) for _, v in sorted(per.items())]
    s = slope(trips, y)
    if s is None or s <= 0: continue
    rows.setdefault(k, []).append((P/1000.0, s, os.path.basename(os.path.dirname(d)) + '/' + os.path.basename(d) + ' s' + seed))
print("%-14s %5s %4s %10s %10s %8s %8s  %s" % ('kernel', 'loops', 'n', 'P med', 'slope med', 'P/slope', 'min-max', 'outliers (P/slope off by > 15 %)'))
for k in sorted(rows):
    r = rows[k]; q = [p/s for p, s, _ in r]
    out = [ '%s %.2f/%.2f' % (n, p, s) for p, s, n in r if abs(p/s - 1) > 0.15 ]
    print("%-14s %5s %4d %10.2f %10.2f %8.2f %4.2f-%4.2f  %s" % (k, lat[k][2], len(r), st.median(p for p, _, _ in r), st.median(s for _, s, _ in r),
          st.median(q), min(q), max(q), '; '.join(out[:4]) + (' (+%d)' % (len(out)-4) if len(out) > 4 else '')))
