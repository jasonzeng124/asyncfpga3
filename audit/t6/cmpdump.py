#!/usr/bin/env python3
"""T6: compare my tsim watched-node histories (auditor net indices) with shard B's simb dump (Lean net indices),
by node name, after TFROM.  usage: cmpdump.py MINE.json B_DUMP.json LEAN_NET.json AUD_NET.json TFROM TMAX"""
import json, sys
M, Bd, L, A, TF, TM = sys.argv[1:7]; TF, TM = int(TF), int(TM)
mine = json.load(open(M))["hist"]; bd = json.load(open(Bd))["nodes"]
ln = json.load(open(L))["nodes"]; an = json.load(open(A))["nodes"]
lidx = {n: i for i, n in enumerate(ln)}
same = diff = 0
for k, (lab, h) in mine.items():
    nm = an[int(k)]; li = lidx[nm]
    a = [t for t, v in h if TF < t <= TM]
    b = [t for t in bd.get(str(li), [False, []])[1] if TF < t <= TM]
    if a == b: same += 1
    else:
        diff += 1; print("DIFF", lab, nm, a[:6], b[:6])
print("watched nodes compared: %d identical, %d differ (flip times in (%d, %d])" % (same, diff, TF, TM))
