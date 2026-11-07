from model import *
def pos(n,s,p):
    if p==0: return g(s,SRC)
    if p==n+1: return g(s,SNK)
    return (s>>(2+4*(p-1)))&15
def pairsets(m,n):
    R=reach(m,n)
    P={}
    for s in R:
        for p in range(n+1):
            P.setdefault(p,set()).add((pos(n,s,p),pos(n,s,p+1)))
    return R,P
for m in ['iso','rt']:
    R,P=pairsets(m,5)
    for p in sorted(P): print(m,p,len(P[p]),sorted(P[p]) if p in (1,2,3) else '')
