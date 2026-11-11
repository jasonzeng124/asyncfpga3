# T64: which links whose SDELAY is defined (bdc's select channels: only these get an SDELAY) are shortened -- DELAY
# (the link's length) or SDELAY below base -- in a candidate sizes file vs its base. Research's new rule (cc95dc0e,
# 2026-11-11): proposals must never shorten a mux delay or a linked select channel's DELAY/SDELAY below base.
# usage: selscan_own.py BASE.vh CAND.vh
import re, sys
def rd(f):
    d = {}
    for l in open(f):
        m = re.match(r'`define (BD_SZ_\S+)\s+(\d+)', l)
        if m: d[m[1]] = int(m[2])
    return d
b, c = rd(sys.argv[1]), rd(sys.argv[2])
sel = sorted(k[:-len('_SDELAY')] for k in b if k.endswith('_SDELAY'))
short = []
for s in sel:
    for k in (s, s + '_SDELAY'):
        if k in b and k in c and c[k] < b[k]: short.append((k, b[k], c[k]))
mux = [(k, b[k], c[k]) for k in b if re.search(r'_UMUX\d+$', k) and k in c and c[k] < b[k]]
print(f"{sys.argv[2].split('/')[-1]} vs {sys.argv[1].split('/')[-1]}: select links {len(sel)}, shortened select DELAY/SDELAY {len(short)}, shortened mux {len(mux)}")
for x in short + mux: print("  ", *x)
