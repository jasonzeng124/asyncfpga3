#!/usr/bin/env python3
"""predecessor dependence (UNTRUSTED): usage pdep.py c PAIR. Per window: the two context-dependent items found by win.py:
(a) the inner head SLICE_X38Y51.B5's alternatives at window start, (b) L entry (reader X26Y65.A6, a=X30Y60.C6 first event of the
main window, b=X31Y65.D6) relative to the window offset."""
import sys, pickle, collections
import numpy as np
sys.path.insert(0, "/tmp/claude-0/win")
from classify import load
import tok
c = int(sys.argv[1]); P = sys.argv[2]; a_, b_ = map(int, P.strip("_").split("_"))
C = load(); nm = C["names"]; ix = nm.index
D = pickle.load(open("/tmp/claude-0/win/ao_c%d_prevanc_cyc_causeanc_dcp%s.pkl" % (c, P), "rb"))
el = D["el"]; xi = {n: i for i, n in enumerate(D["xs"])}; eid = {(n, k): i for i, (n, k, t) in enumerate(el)}
tr, _ = tok.run(a_, b_)
inner = []; first = False; mi = -1
for x in tr:
    if x[0] == "L9": first = True; mi += 1
    elif x[0] == "L10": inner.append((mi, "first" if first else "next", "shift" if x[1] else "exit")); first = False
h = ix("SLICE_X38Y51.B5"); g = ix("SLICE_X38Y51.B6"); d6 = ix("SLICE_X38Y52.D6")
print("inner head %s: per inner window: (main iter, first/next, shift/exit), alternatives of head event 2j, events of B6 so far" % nm[h])
for j, k in enumerate(inner):
    e = eid[(h, 2 * j)]
    alts = [sorted((nm[el[p][0]], el[p][1]) for p in alt) for alt in D["alts"][e]]
    nb = sum(1 for (n, kk, t) in el if n == g and t < el[e][2])
    print("  w%d %s alts %s  | B6 events before: %d, time %d" % (j, k, alts, nb, el[e][2]))
hm = ix("SLICE_X39Y21.C5"); A = ix("SLICE_X30Y60.C6"); B = ix("SLICE_X31Y65.D6"); v = ix("SLICE_X26Y65.A6")
hv = D["VCP"][:, xi[hm]].astype(int); w = np.where(hv == 0, -1, (hv - 1) // 2)
ks = []; cur = None
for x in tr:
    if x[0] == "L9": cur = [0]; ks.append(cur)
    elif x[0] == "L10" and cur: cur[0] += 1
print("main windows: inner count, (a=X30Y60.C6 first event in window) L(v=X26Y65.A6; a, b=X31Y65.D6) - offset(b), VC, VCP, over")
for j in range(len(ks)):
    evs = [e for e in range(len(el)) if el[e][0] == A and w[e] == j]
    offb = sum(1 for e in range(len(el)) if el[e][0] == B and w[e] < j)
    if not evs: continue
    e = evs[0]; k = el[e][1]
    L = min(int(D["VC"][e, xi[B]]), D["OVER"].get(v, {}).get((A, k, B), 99))
    print("  w%d inner%d (prev inner%s): rel L %d  VC %d VCP %d over %s" % (j, ks[j][0], ks[j - 1][0] if j else "-", L - offb, D["VC"][e, xi[B]], D["VCP"][e, xi[B]], D["OVER"].get(v, {}).get((A, k, B))))
