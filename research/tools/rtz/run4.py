import sys,json,collections,bisect
sys.path.insert(0,'.')
from trace_lib import load_vcd
G=sys.argv[1]
ev=load_vcd(G+'/rtz/v6.vcd', keep=lambda n:n.startswith('n'))
hops=json.load(open('lap_chain.json'))[::-1]
def edge(n,t):
    v=[val for tt,val in ev[n] if tt==t]; return {'1':'R','0':'F'}.get(v[-1] if v else '?','?')
def inst(c):
    nm=c['cell']
    if not nm.startswith('urig.udut.'): return 'RIG'
    return nm.split('.')[2]
def role(nm):
    for k,r in (('.rdly.','rdly'),('.udly.','udly'),('.ctl.','ctl'),('.lat.','latch'),('.uack','ack'),('.ua1','arback'),('.ua2','arback'),('.ustate','arb'),('.ugrant','arb')):
        if k in nm: return r
    if '_j.' in nm or nm.split('.')[2].endswith('_j'): return 'join'
    return 'gate'
rows=[(inst(c),role(c['cell']),edge(n,t),t-c['t'],c['wire'],c['arc']) for n,t,c in hops]
tot=sum(r[3] for r in rows)
# polarity runs
runs=[]
for r in rows:
    if runs and runs[-1][0]==r[2]: runs[-1][1]+=r[3]
    else: runs.append([r[2],r[3]])
print('lap',tot,'ps; polarity runs:',len(runs),'; R total',sum(r[3] for r in rows if r[2]=='R'),'F total',sum(r[3] for r in rows if r[2]=='F'))
# per role x edge with wire/arc split
agg=collections.defaultdict(lambda:[0,0,0,0])
for i,ro,e,dt,w,a in rows: x=agg[(ro,e)]; x[0]+=dt;x[1]+=w;x[2]+=a;x[3]+=1
print('role edge   total_ns  wire_ns  cell_ns  hops')
for k,v in sorted(agg.items(),key=lambda x:-x[1][0]): print(f"{k[0]:7} {k[1]}  {v[0]/1e3:8.1f} {v[1]/1e3:8.1f} {v[2]/1e3:8.1f} {v[3]:6}")
# per instance
ai=collections.defaultdict(lambda:{'R':0,'F':0,'n':0})
prev=None
for i,ro,e,dt,w,a in rows:
    ai[i][e]=ai[i].get(e,0)+dt
    if i!=prev: ai[i]['n']+=1
    prev=i
print('\ninstance              rise_ns  fall_ns  visits  ns/visit')
for k,v in sorted(ai.items(),key=lambda x:-(x[1]['R']+x[1]['F']))[:25]:
    print(f"{k:22} {v['R']/1e3:8.1f} {v['F']/1e3:8.1f} {v['n']:6} {(v['R']+v['F'])/1e3/v['n']:8.2f}")
