import sys,json,collections,statistics as st
sys.path.insert(0,'.')
from trace_lib import load_vcd
G=sys.argv[1]
ev=load_vcd(G+'/rtz/v6.vcd', keep=lambda n:n.startswith('n'))
hops=json.load(open('lap_chain.json'))[::-1]
def edge(n,t):
    v=[val for tt,val in ev[n] if tt==t]; return {'1':'R','0':'F'}.get(v[-1] if v else '?','?')
def inst(c):
    nm=c['cell']; return nm.split('.')[2] if nm.startswith('urig.udut.') else 'RIG'
rows=[(inst(c),edge(n,t),t-c['t'],t,c['wire'],c['arc'],c['cell']) for n,t,c in hops]
# iteration marker: entering uori4 on a rising event after something else
marks=[i for i,r in enumerate(rows) if r[0]=='uori4' and r[1]=='R' and (i==0 or rows[i-1][0]!='uori4')]
print('ctz-loop marker visits:',len(marks))
iters=[]
for a,b in zip(marks,marks[1:]):
    seg=rows[a:b]; tot=sum(r[2] for r in seg)
    R=sum(r[2] for r in seg if r[1]=='R'); F=tot-R
    per=collections.Counter()
    for r in seg: per[(r[0],r[1])]+=r[2]
    iters.append((tot,R,F,per,rows[a][3]))
tots=[i[0] for i in iters]
print('iteration ns: median %.2f min %.2f max %.2f n=%d'%(st.median(tots)/1e3,min(tots)/1e3,max(tots)/1e3,len(tots)))
# typical iterations = those within 10% of median
typ=[i for i in iters if abs(i[0]-st.median(tots))<0.1*st.median(tots)]
print('typical n=%d  mean %.2f ns  R %.2f  F %.2f (F share %.1f%%)'%(len(typ),st.mean(i[0] for i in typ)/1e3,st.mean(i[1] for i in typ)/1e3,st.mean(i[2] for i in typ)/1e3,100*st.mean(i[2] for i in typ)/st.mean(i[0] for i in typ)))
agg=collections.Counter()
for i in typ: agg.update(i[3])
print('per typical iteration, ns by (instance, edge):')
for k,v in sorted(agg.items(),key=lambda x:-x[1])[:20]: print('   %-26s %s %6.2f'%(k[0],k[1],v/len(typ)/1e3))
# whole sequence of one typical iteration
i0=typ[len(typ)//2]
a=[k for k,m in enumerate(marks) if rows[m][3]==i0[4]][0]
seg=rows[marks[a]:marks[a+1]]
print('\none typical iteration hop-by-hop (instance edge ns wire arc cell-suffix):')
cur=None
for r in seg:
    print('  %-24s %s %6.3f w%5d a%4d  %s'%(r[0],r[1],r[2]/1e3,r[4],r[5],'.'.join(r[6].split('.')[3:])[:50]))
import collections as C
b=C.Counter(round(t/1e3) for t in tots); print('interval histogram (ns):',sorted(b.items()))
print('sum of intervals %.1f ns of lap 3154.3; first marker at +%.1f ns, last at +%.1f ns'%(sum(tots)/1e3,(rows[marks[0]][3]-19370696)/1e3,(rows[marks[-1]][3]-19370696)/1e3))
long=[i for i in iters if i[0]>60000]
agg=C.Counter()
for i in long: agg.update(i[3])
print('long (ctz-exit + main body) iterations n=%d mean %.1f ns, F share %.1f%%'%(len(long),sum(i[0] for i in long)/len(long)/1e3,100*sum(i[2] for i in long)/sum(i[0] for i in long)))
for k,v in sorted(agg.items(),key=lambda x:-x[1])[:12]: print('   %-26s %s %6.2f'%(k[0],k[1],v/len(long)/1e3))
