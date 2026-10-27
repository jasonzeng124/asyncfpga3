#!/usr/bin/env python3
"""For each GLS O6 edge to value v at time T, find the latest f-change to v at or
before T; apparent delay = T - that time.  Arc (equal delays) vs apparent."""
import sys
log, INIT = sys.argv[1], int(sys.argv[2], 0)
f = lambda s: (INIT >> (int(s[0]) | int(s[1]) << 1 | int(s[2]) << 2)) & 1
fch, prev, outs = [], 0, []
for ln in open(log):
    p = ln.split()
    if p[0] == 'I':
        v = f(p[3])
        if v != prev: fch.append((int(p[1]), v)); prev = v
    elif p[0] == 'O' and p[2] in '01' and int(p[1]) >= 1000: outs.append((int(p[1]), int(p[2])))
app = []
for T, v in outs:
    t0 = max(t for t, w in fch if w == v and t < T)
    app.append(T - t0)
app.sort()
print("%s: %d edges, apparent delay min=%d, #edges with apparent < 124: %d" % (log, len(app), app[0], sum(a < 124 for a in app)))
