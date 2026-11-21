#!/usr/bin/env python3
"""Explicit-state reachability of the bd_mux SI model (C-8f), with the
counter differences the data proof needs.  Used to find the invariant that
OpsMux.lean then checks by `decide`.  Signals (bit order):
 0 xr 1 xa 2 yr 3 ya 4 cr 5 ca 6 s 7 zr 8 za 9 j0 10 j1"""
import itertools, sys
N=11
names="xr xa yr ya cr ca s zr za j0 j1".split()
def bits(v): return {n:(v>>i)&1 for i,n in enumerate(names)}
def enc(d): return sum(d[n]<<i for i,n in enumerate(names))
def allowed(c,n):
    ch=lambda k: c[k]!=n[k]
    if ch('xr') and not (c['xr']==c['xa']): return False
    if ch('yr') and not (c['yr']==c['ya']): return False
    if ch('cr') and not (c['cr']==c['ca']): return False
    if ch('za') and not (c['za']!=c['zr']): return False
    if ch('j0') and not (c['xr']==n['j0'] and (c['cr'] and not c['s'])==n['j0']): return False
    if ch('j1') and not (c['yr']==n['j1'] and (c['cr'] and c['s'])==n['j1']): return False
    if ch('zr') and not (n['zr']==(c['j0'] or c['j1'])): return False
    if ch('xa') and not (c['j0']==n['xa'] and c['za']==n['xa']): return False
    if ch('ya') and not (c['j1']==n['ya'] and c['za']==n['ya']): return False
    if ch('ca') and not (n['ca']==c['za']): return False
    if ch('s') and (c['cr'] or c['ca']) and (n['cr'] or n['ca']): return False
    return True
# state: (bits, dc, dx, dy): dc = #rise cr - #rise zr ; dx = #rise xr - #(c offers with s=0); dy likewise s=1
init=[(enc({k:(0 if k!='s' else sv) for k in names}),0,0,0) for sv in (0,1)]
seen=set(init); todo=list(init)
while todo:
    st=todo.pop(); v,dc,dx,dy=st; c=bits(v)
    for m in range(1<<N):
        n=bits(v^m)
        if not allowed(c,n): continue
        rc = (not c['cr']) and n['cr']; rz=(not c['zr']) and n['zr']
        rx = (not c['xr']) and n['xr']; ry=(not c['yr']) and n['yr']
        c0 = rc and not n['s']; c1 = rc and n['s']
        s2=(v^m, dc+rc-rz, dx+rx-c0, dy+ry-c1)
        if s2 not in seen: seen.add(s2); todo.append(s2)
print("reachable (bits,dc,dx,dy):", len(seen))
byb={}
for v,dc,dx,dy in seen: byb.setdefault(v,set()).add((dc,dx,dy))
print("distinct bit-states:", len(byb), " functional:", all(len(s)==1 for s in byb.values()))
print("dc range", sorted({x[1] for x in seen}), "dx", sorted({x[2] for x in seen}), "dy", sorted({x[3] for x in seen}))
# safety checks
bad=0
for v,dc,dx,dy in seen:
    c=bits(v)
    for m in range(1<<N):
        n=bits(v^m)
        if not allowed(c,n): continue
        if c['xa']!=n['xa'] and c['xa']==c['xr']: bad+=1
        if c['ya']!=n['ya'] and c['ya']==c['yr']: bad+=1
        if c['ca']!=n['ca'] and c['ca']==c['cr']: bad+=1
        if c['zr']!=n['zr'] and c['zr']!=c['za']: bad+=1
print("protocol violations:", bad)
if not all(len(s)==1 for s in byb.values()):
    for v,s in byb.items():
        if len(s)>1: print(bits(v), s); break
if '-dump' in sys.argv:
    for v in sorted(byb): print(v, byb[v])

if '-lean' in sys.argv:
    B=lambda b: 'true' if b else 'false'
    rows=[]
    for v,dc,dx,dy in sorted(seen):
        c=bits(v)
        rows.append("⟨"+", ".join(B(c[n]) for n in names)+f", {dc}, {dx+1}, {dy+1}⟩")
    out=open(sys.argv[sys.argv.index('-lean')+1],'w')
    out.write("def tbl : List MS := [\n  " + ",\n  ".join(rows) + "]\n")
