import sys, collections
exec(open('/tmp/claude-0/-home-user-asyncfpga3/1493a6da-414d-591f-aed7-9ee9f21c4602/scratchpad/rtz/backtrace.py').read())
inv={v:k for k,v in netname.items()}
OUT=inv['urig.out0_req']
def summarize(ch, label):
    hops=[h for h in ch if h[0] not in ('END','STOP')]
    tot=hops[0][1]-hops[-1][2]['t']
    by_edge=collections.Counter(); by_role=collections.Counter(); by_inst=collections.Counter(); wire=arc=0
    for n,t,c in hops:
        dt=t-c['t']
        # edge of the OUTPUT event at this hop
        v=[val for tt,val in ev[n] if tt==t]
        edge='rise' if v and v[-1]=='1' else ('fall' if v and v[-1]=='0' else '?')
        inst,role=classify(c['cell'])
        by_edge[edge]+=dt; by_role[(role,edge)]+=dt; by_inst[(inst,edge)]+=dt
        wire+=c['wire']; arc+=c['arc']
    slack=sum(c['slack'] for n,t,c in hops)
    print(f"== {label}: {len(hops)} hops, {tot} ps; wire {wire} arc {arc} slack {slack}; end={ch[-1][0]} {ch[-1][1] if len(ch[-1])>1 else ''}")
    print('  by edge:', {k:v for k,v in by_edge.items()}, ' fall share %.1f%%' % (100*by_edge['fall']/tot))
    print('  by role/edge:', sorted(((k,v) for k,v in by_role.items()), key=lambda x:-x[1])[:14])
    print('  top instances:', sorted(((k,v) for k,v in by_inst.items()), key=lambda x:-x[1])[:20])
    return hops

t_end=[t for t,v in ev[OUT] if v=='1'][-1]; t_start=[t for t,v in ev[OUT] if v=='1'][0]
ch=chain(OUT,t_end,stop_t=t_start)
hops=summarize(ch,'whole lap (out0_req rise to rise)')
json.dump([(n,t,c) for n,t,c in hops],open('lap_chain.json','w'))
# which loop-marker nets are on the lap chain, and when
onchain=collections.defaultdict(list)
for n,t,c in hops: onchain[n].append(t)
for nm in ['urig.udut.n121_req','urig.udut.n163_req','urig.in_ack','urig.out0_req']:
    print(nm, 'on chain at', len(onchain.get(inv[nm],[])), 'events')
# per-iteration: consecutive rises of a loop marker
for nm in ['urig.udut.n163_req','urig.udut.n121_req']:
    n=inv[nm]; rises=[t for t,v in ev[n] if v=='1']
    per=[]
    for a,b in zip(rises,rises[1:]):
        ch=chain(n,b,stop=lambda nn,tt,n=n,a=a: (nn==n and tt<=a) or tt<a-1)
        hops=[h for h in ch if h[0] not in ('END','STOP')]
        ended_on_self = ch[-1][1]==n
        fall=sum(t-c['t'] for x,t,c in hops if [v for tt,v in ev[x] if tt==t][-1:]==['0'])
        per.append((b-a, ended_on_self, fall))
    print(nm, len(per), 'intervals; period ps:', sorted(set(p[0] for p in per))[:12])
    print('   chain closes on itself (true cycle):', sum(p[1] for p in per),'of',len(per))

