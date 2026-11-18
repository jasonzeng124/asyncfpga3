import os,re,statistics as st,math,glob
R='/root/agentB/s4/results/suite4'
rows={}
for t in range(1,33):
    f=f'{R}/{t}/result.txt'
    if not os.path.exists(f): continue
    s=open(f).read()
    m=re.match(r'(\w+) (\d+) status=(\S+)',s)
    k,seed,stt=m.groups()
    P=re.search(r'P=(\d+)',s); d=re.search(r'draws=(\d+)/(\d+)',s)
    # count draws.txt lines independently
    dl=open(f'{R}/{t}/draws.txt').read().splitlines() if os.path.exists(f'{R}/{t}/draws.txt') else []
    npass=sum(1 for l in dl if ':: PASS' in l); nall=sum(1 for l in dl if l.startswith('draw '))
    rows.setdefault(k,[]).append((int(seed),stt,int(P.group(1))/1000 if P else None,npass,nall,d.groups() if d else None, re.search(r'rule=(\S+)',s).group(1) if 'rule=' in s else ''))
dyn={'collatz':14.05,'collatz64':17.84,'ipow':49.98,'xorshift':12.73}
meas=[];allr=[]
for k,v in rows.items():
    v.sort(); js=[x for x in v if x[1]=='PASS']
    Ps=[x[2] for x in js]
    print(k,'tasks w/result',len(v),'judged',len(js),'draws',sum(x[3] for x in js),'/',sum(x[4] for x in js),
      'median %.3f range %.2f-%.2f'%(st.median(Ps),min(Ps),max(Ps)),'clean',sum(1 for x in js if x[6]=='clean'))
    for x in v: print('   ',x)
    r=st.median(Ps)/dyn[k]; print('   ratio %.3f'%r); allr.append(r)
    if k!='ipow': meas.append(r)
g=lambda a: math.exp(sum(map(math.log,a))/len(a))
print('geomean measured %.3f all %.3f'%(g(meas),g(allr)))
