#!/usr/bin/env python3
"""reach of causes beyond 1 window (UNTRUSTED): usage reach.py c PAIR.  For each cause/RT source more than one main-loop
window back: is it rst, and is it the LAST event of its node (a node that has gone quiet)?"""
import sys, pickle, collections
import numpy as np
sys.path.insert(0, "/tmp/claude-0/win")
from classify import load
c = int(sys.argv[1]); P = sys.argv[2]
C = load(); nm = C["names"]
D = pickle.load(open("/tmp/claude-0/win/ao_c%d_prevanc_cyc_causeanc_dcp%s.pkl" % (c, P), "rb"))
el = D["el"]; xi = {n: i for i, n in enumerate(D["xs"])}; cnt = collections.Counter(n for n, k, t in el)
for hn in ("SLICE_X39Y21.C5", "SLICE_X38Y51.B5"):
    h = nm.index(hn); hv = D["VCP"][:, xi[h]].astype(int); w = np.where(hv == 0, -1, (hv - 1) // 2)
    st = collections.Counter(); ex = collections.Counter()
    for e in range(len(el)):
        srcs = [(p, "cause") for alt in D["alts"][e] for p in alt] + [(p, "RT") for p in D["rt"].get(e, [])]
        for p, kind in srcs:
            d = int(w[e] - w[p])
            if d < 2: continue
            n, k, t = el[p]
            last = k == cnt[n] - 1
            cls = "rst" if nm[n] == "SLICE_X2Y29.DQ" else ("quiet-node (cause is its last event)" if last else "ACTIVE node")
            st[(kind, cls)] += 1
            if cls == "ACTIVE node": ex[(kind, nm[el[e][0]], nm[n], d)] += 1; st[(kind, "ACTIVE reach", d)] += 1
    print("%s c=%d head %s: reach>=2 sources %s" % (P, c, hn, dict(st)))
    for x, v in ex.most_common(6): print("   ACTIVE example", x, v)
