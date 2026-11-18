#!/usr/bin/env python3
"""runts.py DIR REGEX [MAXW_PS] [T0 T1]: high pulses narrower than MAXW (default 1000 ps) on nets matching REGEX."""
import sys, re, collections
d, rx = sys.argv[1], re.compile(sys.argv[2])
mw = int(sys.argv[3]) if len(sys.argv) > 3 else 1000
T0 = int(sys.argv[4]) if len(sys.argv) > 4 else 0
T1 = int(sys.argv[5]) if len(sys.argv) > 5 else 1 << 62
names = {}
for ln in open(f"{d}/nets.map"):
    p = ln.split(None, 1)
    if len(p) == 2 and not ln.startswith("#") and rx.search(p[1]): names[p[0]] = p[1].strip()
want = {}; hist = collections.defaultdict(list); t = 0
for ln in open(f"{d}/dump.vcd"):
    if ln.startswith("$var"):
        p = ln.split()
        if p[4] in names: want[p[3]] = names[p[4]]
        continue
    if not ln or ln[0] in "$ \n": continue
    if ln[0] == "#": t = int(ln[1:]); continue
    if ln[0] in "01xz":
        i = ln[1:].strip()
        if i in want: hist[i].append((t, ln[0]))
tot = collections.Counter()
for i, h in hist.items():
    for k in range(len(h) - 1):
        if h[k][1] == "1" and h[k + 1][1] == "0" and h[k + 1][0] - h[k][0] < mw and T0 <= h[k][0] <= T1:
            tot[want[i]] += 1
            print(f"RUNT {want[i]:45s} at {h[k][0]} width {h[k + 1][0] - h[k][0]} ps")
print("TOTAL", dict(tot))
