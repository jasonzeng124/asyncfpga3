import re,math,os
R='/root/agentM/rs/research/'
lines=open('/root/agentM/v10sec.md').read().split('\n')
start=[i for i,l in enumerate(lines) if l.startswith('| kernel | status')][0]
rows={}
for l in lines[start+2:]:
    if not l.startswith('|'): break
    c=[x.strip() for x in l.strip('|').split('|')]
    rows[c[0]]=c
bound={}
for l in open(R+'data/suite/dynamatic/dynamatic_est.tsv'):
    if l.startswith('#'): continue
    k=l.split('\t')[0]; m=re.search(r'simulated ([0-9.]+) cycles per iteration.*?any placement >= ([0-9.]+)',l)
    if m: bound[k]=(float(m.group(1)),float(m.group(2)))
def per(k):
    t=open(R+f'data/suite/dynamatic/routed/{k}/route.txt').read()
    ps=[float(x) for x in re.findall(r'seed \d+ Fmax [0-9.]+ MHz period ([0-9.]+)',t)]
    m=re.search(r'mean ([0-9.]+)',t); return ps,float(m.group(1))
def cyc(k):
    t=open(R+f'data/suite/dynamatic/routed/{k}/est_summary.txt').read()
    m=re.search(r'cycles per iteration: ([0-9.]+)',t); return float(m.group(1)) if m else None
ref={l.split('\t')[0]:l.rstrip('\n').split('\t') for l in open(R+'tools/suite/dynamatic_ref.tsv') if not l.startswith('#')}
sel=[];out=[]
for k,c in rows.items():
    if c[1]!='PASS': continue
    try: ratio=float(c[8].split()[0])
    except: continue
    if 'not comparable' in c[8]: continue
    pm=re.search(r'([0-9.]+) \(',c[4]); P=float(pm.group(1))
    dyn=float(c[7].split()[0]); tag=c[7]
    ps,mean=per(k) if os.path.exists(R+f'data/suite/dynamatic/routed/{k}/route.txt') else ([],None)
    cy=cyc(k) if mean else None
    b=bound.get(k,(None,None))[1]
    dynb = mean*b if (mean and b) else None
    if k=='gcd': pass
    r1=P/dyn; r2=P/dynb if dynb else None
    sel.append((k,P,dyn,tag,ratio,r1,mean,cy,b,dynb,r2,len(ps)))
print(len(sel))
for s in sel: print('%-16s P=%7.2f dyn=%7.2f [%s] tbl=%.2f rec=%.3f | mean=%s cyc=%s bound=%s dynB=%s r2=%s nseeds=%d'%(s[0],s[1],s[2],s[3][:20],s[4],s[5],s[6],s[7],s[8],None if s[9] is None else round(s[9],2),None if s[10] is None else round(s[10],3),s[11]))
gm=lambda v: math.exp(sum(map(math.log,v))/len(v))
print('GM on-merges (recomputed P/dyn):',gm([s[5] for s in sel]),' table ratios:',gm([s[4] for s in sel]))
v=[s[10] for s in sel if s[10]]; print('GM bound n=',len(v),gm(v))
# without test_stdint
v2=[s for s in sel if s[0]!='test_stdint']; print('excl test_stdint n',len(v2),gm([s[5] for s in v2]), gm([s[10] for s in v2 if s[10]]))
# contributions
import statistics
for name,idx in (('onmerge',5),('bound',10)):
    L=sorted([(math.log(s[idx]),s[0]) for s in sel if s[idx]]); print(name,'most negative',[(n,round(math.exp(x),2)) for x,n in L[:6]],'most positive',[(n,round(math.exp(x),2)) for x,n in L[-6:]])
v2=[s for s in sel if s[0]!='test_stdint' and s[10]]
top=sorted(v2,key=lambda s:-s[10])[:5]; print('top5',[(s[0],round(s[10],1)) for s in top])
rest=[s[10] for s in v2 if s not in top]; print('without top5 n',len(rest),gm(rest))
one=[s for s in v2 if s[7] and abs(s[7]-1.0)<0.005]; print('one-cycle n',len(one),gm([s[10] for s in one]),[s[0] for s in one])
