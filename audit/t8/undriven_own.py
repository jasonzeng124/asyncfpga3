#!/usr/bin/env python3
"""undriven_own.py (audit T8): backward cone of the kernel outputs in the decoded net, cut at the boundary inputs;
prints multiply-driven nodes and every cone node with no driver gate.  python3 -I undriven_own.py NET.json BND.json"""
import json,sys
N=json.load(open(sys.argv[1])); B=json.load(open(sys.argv[2]))['boundary']
idx={n:i for i,n in enumerate(N['nodes'])}
drv={}
for g in N['gates']: drv.setdefault(g['out'],[]).append(g)
multi=[n for n,l in drv.items() if len(l)>1]
print("nodes",len(N['nodes']),"gates",len(N['gates']),"multiply-driven",len(multi))
def nd(x):
    if x in idx: return idx[x]
    raise KeyError(x)
ins=[B[k] for k in ('rst','req','out0_ack')]+B['a_data']+B['b_data']
stop=set(nd(x) for x in ins if x!='const0')
outs=[B[k] for k in ('a_ack','b_ack','start_ack','out0_req','pend_ack')]+B['out0_data']
seen=set(); st=[nd(x) for x in outs]; und=[]
while st:
    n=st.pop()
    if n in seen: continue
    seen.add(n)
    if n in stop: continue
    if n not in drv: und.append(N['nodes'][n]); continue
    for g in drv[n]: st.extend(g['ins'])
print("cone nodes",len(seen),"stop nodes reached",len(stop&seen),"of",len(stop),"undriven in cone",len(und), und[:10])
