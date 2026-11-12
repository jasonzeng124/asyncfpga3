from model import *
from proj import pos, pairsets
import itertools
def build(m):
    R,P=pairsets(m,5)
    return P[0],P[1],P[5]
def states(m,n,P0,PM,PN):
    # enumerate chains
    res=[]
    def rec(p,vals):
        if p==n+2:
            s=vals[0]|(vals[-1]<<1)
            for q in range(1,n+1): s|=vals[q]<<(2+4*(q-1))
            res.append(s); return
        rng = [0,1] if p in (0,n+1) else range(16)
        for v in rng:
            if p>0:
                if p==1: S=P0
                elif p==n+1: S=PN
                else: S=PM
                if (vals[-1],v) not in S: continue
            rec(p+1,vals+[v])
    rec(0,[])
    return res
def good(m,n,s,I):
    N=nn(n); bad=[]
    for y in range(N):
        if not enabled(m,n,s,y): continue
        t=s^(1<<y)
        if t not in I: bad.append(('notclosed',y))
        for x in range(N):
            if x!=y and exc(m,n,s,x) and not exc(m,n,t,x): bad.append(('haz',x,y))
    return bad
for m in ['iso','rt']:
    P0,PM,PN=build(m)
    for n in range(1,7):
        S=states(m,n,P0,PM,PN); I=set(S)
        R=reach(m,n) if n<=5 else None
        nb=0;ex=None
        for s in S:
            bb=good(m,n,s,I)
            if bb: nb+=1; ex=ex or (s,bb)
        print(m,n,len(S), len(R) if R else '-', 'bad',nb, ex)
