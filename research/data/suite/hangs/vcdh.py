#!/usr/bin/env python3
"""vcdh.py DIR REGEX [T0 T1]: transitions of every net whose routed-json name matches REGEX, in [T0, T1] ps."""
import sys, re, collections
d, rx = sys.argv[1], re.compile(sys.argv[2])
T0 = int(sys.argv[3]) if len(sys.argv) > 3 else 0
T1 = int(sys.argv[4]) if len(sys.argv) > 4 else 1 << 62
names = {}
for ln in open(f"{d}/nets.map"):
    if ln.startswith("#"): continue
    p = ln.split(None, 1)
    if len(p) == 2 and rx.search(p[1]): names[p[0]] = p[1].strip()
want = {}
hist = collections.defaultdict(list)
t = 0
with open(f"{d}/dump.vcd") as f:
    for ln in f:
        if ln.startswith("$var"):
            p = ln.split()
            if p[4] in names: want.setdefault(p[3], []).append(p[4])
            continue
        if not ln or ln[0] in "$ \n": continue
        if ln[0] == "#":
            t = int(ln[1:])
            if t > T1: break
            continue
        c = ln[0]
        if c in "01xzXZ":
            i = ln[1:].strip(); v = c.lower()
        elif c == "b":
            v, i = ln[1:].split(); v = v.lower()
        else: continue
        if i in want: hist[i].append((t, v))
for i, ns in sorted(want.items(), key=lambda kv: names[kv[1][0]]):
    h = hist.get(i, [])
    before = [x for x in h if x[0] < T0]
    inwin = [x for x in h if T0 <= x[0] <= T1]
    s0 = before[-1][1] if before else "?"
    print(f"{names[ns[0]][:60]:60s} [{s0}] " + " ".join(f"{tt}:{v}" for tt, v in inwin[:14]))
