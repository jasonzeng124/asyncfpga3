#!/usr/bin/env python3
"""T145: ns/iter slope (as t140/fit2.py) at CARRY 0.20 and 1.0; prints both and the relative change. usage: slope.py KERNEL A B"""
import sys, numpy as np
k, fa, fb = sys.argv[1:4]
def rows(p):
    out = []
    for l in open(p):
        f = l.split()
        if not (len(f) > 12 and f[0].isdigit()): continue
        try:
            if k == 'ipow':
                if f[5] == f[4] and f[8] == '2': out.append((int(f[3]), int(f[10])))
            elif int(f[4], 16) == int(f[3]) and f[7] == '2' and int(f[9]) >= 50: out.append((int(f[3]), int(f[9])))
        except ValueError: pass
    return out
s = []
for p in (fa, fb):
    r = rows(p); X, Y = np.array([a for a, _ in r]), np.array([b for _, b in r]); s.append((10 * np.polyfit(X, Y, 1)[0], len(r)))
print(f"{k}: CARRY 0.20 {s[0][0]:.2f} ns/iter ({s[0][1]} vectors), CARRY 1.0 {s[1][0]:.2f} ({s[1][1]}): change {100*(s[1][0]/s[0][0]-1):+.1f} %")
