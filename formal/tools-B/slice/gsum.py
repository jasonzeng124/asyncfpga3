#!/usr/bin/env python3
"""[slice diag] failing guards grouped by (side, data node z, claim anchor), with the worst margin (ps; -inf = no Sep/Up).
usage: gsum.py dir"""
import sys, pickle, collections
D = sys.argv[1]; P = pickle.load(open(D + "/dl_c0.pkl", "rb")); nm = pickle.load(open(D + "/model.pkl", "rb"))["names"]
grp = collections.defaultdict(list)
for x in P["G"]:
    if len(x) != 7: continue
    v, z, ms, me, cz, st, en_ = x
    for side, m, anc in (("start", ms, cz.get("A")), ("end", me, cz.get("B"))):
        if m < 0: grp[(side, nm[z])].append(m)
for k, ms in sorted(grp.items(), key=lambda kv: -len(kv[1])):
    print("  %-5s z=%-16s guards %3d  worst margin %s" % (k[0], k[1], len(ms), min(ms) if min(ms) > -1e18 else "-inf"))
