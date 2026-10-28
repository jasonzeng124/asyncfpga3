import re,sys
from fractions import Fraction as Fr
K=open(sys.argv[1]).read()
data={}
for m in re.finditer(r'def v_(g\w+?_merge\w+?_uarb\d) : E → Quad\n(.*?)\n\n',K,re.S):
    data[m.group(1)]={a:tuple(int(x) for x in v) for a,*v in re.findall(r'\| \.(\w+) => \((\d+), (\d+), (\d+), (\d+)\)',m.group(2))}
forms={}
for m in re.finditer(r'def F_(\w+) : Form := ⟨\[(.*?)\], \[(.*?)\], (\d+), (\d+), (\w+)⟩',K):
    n,P,Q,a,b,sf=m.groups()
    forms[n]=([x.strip()[1:] for x in P.split(',')],[x.strip()[1:] for x in Q.split(',')],int(a),int(b),sf=='true')
def kstar(v,f,rd):
    P,Q,a,b,_=f; best=None
    for s in (0,1):
        def arc(e,side):
            q=v[e]
            if rd=='lit': return (q[0],q[3])[s]
            return ((q[1],q[3]) if side=='P' else (q[0],q[2]))[s]
        D=sum(arc(e,'P') for e in P); R=sum(arc(e,'Q') for e in Q)
        k=Fr(R+b-D-a,R+D)
        best=k if best is None or k<best else best
    return best
for rd in ('lit','cons'):
    allr=[(kstar(v,f,rd),arb,n) for arb,v in data.items() for n,f in forms.items()]
    print(rd,len(allr),'min all',min(allr),float(min(allr)[0]))
    srv=[x for x in allr if not forms[x[2]][4]]
    print(rd,'min srv',min(srv),float(min(srv)[0]))
    print(rd,'neg',sorted((float(k),a,n) for k,a,n in allr if k<0))
    for kk,name in ((Fr(1,11),'1/11'),(Fr(383,1927),'kE')):
        print(rd,'fail at',name,sum(1 for k,a,n in allr if k<kk))
