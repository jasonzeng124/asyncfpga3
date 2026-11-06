#!/usr/bin/env python3
"""Shard B (UNTRUSTED): for shard C's persistence-violation pairs (node n, re-enabler m; tools/huff/out_persist_walks.txt),
scan a timed simb.py dump: every episode in which n's C inputs' SOURCES (celemtab polarity) all show the value
opposite to n's output (n excited), and the episode ends (some input source returns) before n toggles. Reports per
pair the number of excited episodes, how many were withdrawn before n moved, and the shortest excitation-to-toggle
time of the others. usage: persist_timed.py NET.json CELEM.json PAIRS.txt DUMP.json"""
import json, sys
from bisect import bisect_right
N = json.load(open(sys.argv[1])); g = N["gates"]
C = json.load(open(sys.argv[2])); C = C["rows"] if isinstance(C, dict) else C
byname = {r["name"]: r for r in C}
D = json.load(open(sys.argv[4]))["nodes"]
def hist(n): return D.get(str(n), [False, []])
def val(n, t): v0, ts = hist(n); return v0 ^ (bisect_right(ts, t) % 2 == 1)
for line in open(sys.argv[3]):
    cnt, a, _, b = line.split()
    nm = a.replace(".", "LUT.O").replace("6", "6", 1)
    sl, lut = a.split("."); nm = "%s.%sLUT.O6" % (sl, lut[0])
    r = byname.get(nm)
    if r is None: print(line.strip(), "-> not a celemtab C-element"); continue
    q = r["q"]; ins = [(r["srcs"][i], p) for i, p in zip(r["ci"], r["pol"])]
    times = sorted({t for s, _ in ins for t in hist(s)[1]} | set(hist(q)[1]))
    exc = 0; withdrawn = 0; minlat = None
    for t in times:
        e = [val(s, t) ^ bool(p) for s, p in ins]
        if all(x == e[0] for x in e) and e[0] != val(q, t):
            # excited at t: does q toggle before any input source changes?
            qts = hist(q)[1]; k = bisect_right(qts, t); tq = qts[k] if k < len(qts) else None
            tin = min([u for s, _ in ins for u in hist(s)[1] if u > t] or [10**15])
            exc += 1
            if tq is None or tin < tq: withdrawn += 1
            else: minlat = tq - t if minlat is None or tq - t < minlat else minlat
    print("%-18s by %-16s walks %3s: excited %d, withdrawn before toggling %d, min excitation->toggle %s ps" % (a, b, cnt, exc, withdrawn, minlat))
