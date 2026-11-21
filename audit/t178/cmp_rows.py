import re,sys
rd={}
for l in open(sys.argv[1]):
    if l.startswith('| ') and not l.startswith('| kernel'):
        c=[x.strip() for x in l.strip().strip('|').split('|')]
        if len(c)>5: rd[c[0]]=c
    if l.startswith('**PREVIOUS'): break
mine={}
for l in open(sys.argv[2]):
    m=re.match(r'^(\w+)\s+(PASS|UNFINISHED|WRONG|NO RESULT)(.*)',l)
    if m: mine[m.group(1)]=(m.group(2),m.group(3))
print('readme rows',len(rd),'mine',len(mine))
num=lambda s:[x for x in re.findall(r'\d+\.\d+|\d+',s)]
bad=0
for k in sorted(set(rd)|set(mine)):
    if k not in rd or k not in mine: print('MISSING',k,k in rd,k in mine); bad+=1; continue
    c=rd[k]; st,rest=mine[k]
    rst='PASS' if c[1]=='PASS' else c[1].split(' (')[0]
    if rst!=st: print('STATUS',k,rst,st); bad+=1; continue
    if st=='NO RESULT': continue
    m=re.match(r' (\d+)\+(\d+)/(\d+) (\d+)/(\d+);(\d+)/(\d+) P=(.*?) \[(.*?)\] lat=(\S+) dyn=(\S+) ratio=(\S+) L=(.*?) lr=(\S+)',rest)
    a,b,n,c1,c2,n1,n2,P,Pn,lat,dyn,ratio,L,lr=m.groups()
    ok=[]
    ok.append(c[2]=='%s + %s / %s'%(a,b,n))
    dc='%s / %s'%(c1,c2) if c2!='0' else '-'; dn='%s / %s'%(n1,n2) if n2!='0' else '-'
    ok.append(c[3]=='%s; %s'%(dc,dn))
    ok.append(num(c[4].split('[')[0])[:3]==num(P)[:3] if P!='-' else c[4].startswith('-'))
    ok.append((num(c[4].split('[')[1])[:3]==num(Pn)[:3]) if '[' in c[4] else Pn=='-')
    ok.append(c[5]==lat)
    ok.append(c[8].split(' ')[0]==ratio if ratio!='-' else c[8]=='-')
    ok.append(num(c[10].split('[')[0])[:3]==num(L)[:3])
    ok.append(c[12].split(' ')[0]==lr if lr!='-' else c[12]=='-')
    if not all(ok): bad+=1; print('DIFF',k,ok,'| readme:',c[2:6],c[8],c[10][:40],c[12],'| mine:',rest[:200])
print('mismatching rows',bad)
