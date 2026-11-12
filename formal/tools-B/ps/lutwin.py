#!/usr/bin/env python3
"""Shard B (UNTRUSTED), 2026-11-07: LUT pins of a generated NetPS whose admissible-delay window (integer delays, g = 1)
holds fewer than w delays, per corner c and scatter kappa. On such a pin, SpecRunt's H_RUNT(w) FORBIDS a source pulse of
width in [#delays, w) (Formal.Cells.RuntForbid.runt_forbids). Only support pins (the INIT depends on the pin) count.
usage: lutwin.py formal/lean/Formal/Target/NetPS"""
import re,glob,math,sys
pat=re.compile(r'⟨"([^"]*LUT\.O[56])", (\d+), (\d+), \[([^\]]*)\], \[(.*)\], (\d+)⟩')
arc=re.compile(r'⟨(\d+), (\d+), (\d+), (\d+)⟩')
pins=[]
for f in sorted(glob.glob(sys.argv[1]+'/G*.lean')):
    for l in open(f):
        m=pat.search(l)
        if not m: continue
        k=int(m.group(2)); init=int(m.group(3))
        ins=[int(s) for s in m.group(4).split(',')] if m.group(4).strip() else []
        arcs=[tuple(map(int,a)) for a in arc.findall(m.group(5))]
        for p,(a,src) in enumerate(zip(arcs,ins)):
            # does INIT depend on pin p?
            dep=any(((init>>x)&1)!=((init>>(x|(1<<p)))&1) for x in range(1<<k) if not x>>p&1)
            pins.append((m.group(1),p,src,a,dep))
print("LUT pins",len(pins),"support pins",sum(1 for x in pins if x[4]))
def npts(a,c,k):
    fmin,fmax,smin,smax=a
    lo=(1-k)*((1-c)*fmin+c*smin); hi=(1+k)*((1-c)*fmax+c*smax)
    return math.floor(hi)-math.ceil(lo)+1
for w in (20,):
  for c in (0,0.5,1):
    for k in (0,0.05,0.1,0.15,0.2,0.3):
        n=sum(1 for x in pins if x[4] and npts(x[3],c,k)<w)
        print(f"w={w} c={c} kappa={k}: support LUT pins with <{w} admissible delays: {n}")
