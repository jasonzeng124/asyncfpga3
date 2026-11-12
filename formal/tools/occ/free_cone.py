import json, collections, sys
sys.setrecursionlimit(1000000)
net=json.load(open('net.json')); G=net['gates']; N=net['nodes']
BJ=json.load(open('bnd.json')); idx={n:i for i,n in enumerate(N)}; ENV=set(idx[x] for x in BJ['env'])
outs={}
for i,g in enumerate(G): outs[g.get('out',i)]=i
print('gates',len(G),'nodes',len(N), 'sample gate keys', list(G[0].keys()))
print('out==index for all:', all(g['out']==i for i,g in enumerate(G)))
driven=set(g['out'] for g in G)
free=[v for v in range(len(N)) if v not in driven and v not in ENV]
print('free (undriven, non-env) nodes:', len(free))
# readers through copy chains
def is_copy(g): return g['k']==1 and g['init']==2
readers=collections.defaultdict(list)
for i,g in enumerate(G):
    for u in g['ins']: readers[u].append(i)
# forward closure from free nodes through copies to first logic gates
reach_logic=collections.Counter(); ex={}
for f in free:
    st=[f]; seen=set()
    while st:
        u=st.pop()
        for r in readers[u]:
            if r in seen: continue
            seen.add(r)
            if is_copy(G[r]) and r not in ENV: st.append(G[r]['out'])
            else:
                reach_logic[f]+=1; ex.setdefault(f, N[G[r]['out']])
print('free nodes reaching some logic gate:', len(reach_logic))
for f in list(reach_logic)[:15]: print(' ', N[f], '->', ex[f])
B=BJ['boundary']
bouts=set()
for k in ('a_ack','b_ack','start_ack','out0_req'):
    if k in B: bouts.add(idx[B[k]])
for nm in B.get('out0_data',[]): bouts.add(idx[nm])
# forward cone of all free nodes through all gates
cone=set(); st=list(reach_logic)
while st:
    u=st.pop()
    for r in readers[u]:
        o=G[r]['out']
        if o in cone or o in ENV: continue
        cone.add(o); st.append(o)
print('forward cone size of the 55 free nodes:', len(cone))
print('boundary outputs in cone:', [N[b] for b in bouts if b in cone][:10], 'of', len(bouts))
print('keys', list(B.keys()))
