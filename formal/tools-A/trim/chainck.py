#!/usr/bin/env python3
# chainck.py NET.json SITE...: for each changed LUT site (FASM name), in the decoded netlist: the source of its one live
# pin, whether a LUT reading that same source drives the entry (the dead predecessor), and the live line length from
# the entry (follow the LUT that reads the previous element and the same source). Shard A, 2026-11-20.
import json,sys,re
net=json.load(open(sys.argv[1])); changed=sys.argv[2:]
G=net['gates']; drv={}
for i,g in enumerate(G): drv.setdefault(g['out'],i)
readers={}
for i,g in enumerate(G):
    for n in g['ins']: readers.setdefault(n,[]).append(i)
def src(n,seen=0):   # follow pip / hop copies back to a logic driver
    while True:
        i=drv.get(n)
        if i is None: return ('undriven',n)
        g=G[i]
        if g['kind'] in ('pip','hop') and g['k']==1: n=g['ins'][0]; continue
        return i
def fwd(n):   # logic gates fed by node n through copies
    out=[];st=[n];seen=set()
    while st:
        x=st.pop()
        if x in seen: continue
        seen.add(x)
        for i in readers.get(x,[]):
            g=G[i]
            if g['kind'] in ('pip','hop') and g['k']==1: st.append(g['out'])
            else: out.append(i)
    return out
def deps(v,n=6): return [i for i in range(n) if any(((v>>x)&1)!=((v>>(x^(1<<i)))&1) for x in range(1<<n))]
# site lookup: FASM 'TILE.SLICEL_X0.DLUT' -> lut6 gate with prov tile & lut, slice index by x order
bytile={}
for i,g in enumerate(G):
    if g['kind']=='lut6': bytile.setdefault((g['prov']['tile'],g['prov']['lut']),[]).append(i)
def gate_of(f):
    t,s,l=f.split('.'); c=sorted(bytile[(t,l[0])],key=lambda i:int(re.search(r'X(\d+)Y',G[i]['prov']['site']).group(1)))
    return c[int(s[-1])] if len(c)>1 else c[0]
for f in changed:
    i=gate_of(f); g=G[i]; d=deps(g['init'])
    assert len(d)==1, (f,d)
    K=src(g['ins'][d[0]])
    # downstream chain: next element = a lut reading this element's output and K
    n=1; cur=i; path=[G[i]['name']]
    while True:
        nx=[j for j in fwd(G[cur]['out']) if G[j]['kind']=='lut6' and any(src(G[j]['ins'][p])==K for p in deps(G[j]['init']))]
        if len(nx)!=1: break
        cur=nx[0]; n+=1; path.append(G[cur]['name'])
    # the dropped pin: which pin of the untrimmed function? predecessor = a lut that reads K too
    preds=[j for j in fwd(G[K]['out']) if G[j]['kind']=='lut6' and j!=i and any(src(G[j]['ins'][p])==K for p in deps(G[j]['init']))] if isinstance(K,int) else []
    feeds_entry=[j for j in preds if i in fwd(G[j]['out'])]
    print(f"{f}: kept pin A{d[0]+1} <- {G[K]['name'] if isinstance(K,int) else K}; live line from entry = {n} elements; "
          f"a LUT reading the same source feeds the entry (dead predecessor): {'yes' if feeds_entry else 'NO'}")
