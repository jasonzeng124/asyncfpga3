#!/usr/bin/env python3
"""[slice diag] for each remaining control local-check failure (final round of aodiag/ao pickle), the failing TO rows
at the same reader v (L entries lowered there), with their margins Sep - need (ps). usage: ctrlroots.py dir [pkl]"""
import sys, pickle, collections
D = sys.argv[1]; P = pickle.load(open(D + "/" + (sys.argv[2] if len(sys.argv) > 2 else "aodiag_c0_prevanc_cyc_causeanc_dcp.pkl"), "rb"))
M = pickle.load(open(D + "/model.pkl", "rb")); nm = M["names"]
byv = collections.defaultdict(list)
for r in P["rows_fail"]: byv[r[1]].append(r)
for (v, kind, nn, Dv) in P["fails"]:
    print("%s %s n=%s D=%s" % (nm[v], kind, nn, [nm[u] for u in Dv]))
    for m_, v_, a, k, b, mb, s, need in sorted(byv[v], key=lambda r: r[0])[:6]:
        print("    TO row lowered: a=%s(%d) b=%s(%d) Sep=%s need=%d margin %s" % (nm[a], k, nm[b], mb, s, need, m_))
