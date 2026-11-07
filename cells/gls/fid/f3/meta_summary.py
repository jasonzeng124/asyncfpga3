#!/usr/bin/env python3
"""META/FFMETA lines of a GLS_FID run, grouped by RTL cell (names.map).
Usage: meta_summary.py names.map run.log"""
import collections, re, sys
nm = {}
for l in open(sys.argv[1]):
    p = l.split()
    if len(p) == 2:
        nm[p[0]] = p[1]
cnt = collections.defaultdict(collections.Counter)
tr = collections.defaultdict(list)
R = re.compile(r"^(FF)?META \S*?\.(c_\d+)\S* t=\d+ .*?(?:runt_val=(\S) )?-> (\S) after \+?(\d+)")
for l in open(sys.argv[2]):
    m = R.match(l)
    if not m:
        if l.startswith(("CH ", "X on")):
            print(l.rstrip())
        continue
    key = ("FF " if m.group(1) else "LUT ") + re.sub(r"\[\d+\]", "[*]", nm.get(m.group(2), m.group(2)))
    if m.group(1):
        cnt[key]["->" + m.group(4)] += 1
    else:
        cnt[key]["commit" if m.group(3) == m.group(4) else "reject"] += 1
    tr[key].append(int(m.group(5)))
for k in sorted(cnt, key=lambda k: -sum(cnt[k].values())):
    t = sorted(tr[k])
    print("%-40s %4d events %s  t_r median %d max %d ps" % (k, sum(cnt[k].values()), dict(cnt[k]),
                                                            t[len(t) // 2], t[-1]))
