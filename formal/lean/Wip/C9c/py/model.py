import sys
INIT=0x00B200B200B200B2
def g(s,i): return (s>>i)&1
def c(k): return 2+4*k
def b(k): return 3+4*k
def w(k): return 4+4*k
def f(k): return 5+4*k
SRC,SNK=0,1
def nn(n): return 2+4*n
def nextVal(m,n,s,i):
    if i==SRC: return 1-g(s,w(0))
    if i==SNK: return g(s,b(n-1))
    k=(i-2)//4; r=(i-2)%4
    if r==0:
        A = g(s,SRC) if k==0 else g(s,b(k-1))
        B = g(s,SNK) if k+1==n else g(s,w(k+1))
        Q = g(s,c(k)) if m=='iso' else g(s,f(k))
        return (INIT>>(A+2*B+4*Q))&1
    if r==1 or r==2: return g(s,c(k))
    return g(s,i) if m=='iso' else g(s,c(k))
def exc(m,n,s,i): return nextVal(m,n,s,i)!=g(s,i)
def reader(n,i):
    if i==SRC: return 0
    if i==SNK: return n-1
    k=(i-2)//4; r=(i-2)%4
    if r==1: return k+1 if k+1<n else None
    if r==2: return k-1 if k>=1 else None
    return None
def allowed(m,n,s,i):
    if m!='rt': return True
    k=reader(n,i)
    if k is None: return True
    return g(s,f(k))==g(s,c(k))
def enabled(m,n,s,i): return i<nn(n) and exc(m,n,s,i) and allowed(m,n,s,i)
def reach(m,n):
    seen={0}; fr=[0]
    while fr:
        nf=[]
        for s in fr:
            for i in range(nn(n)):
                if enabled(m,n,s,i):
                    t=s^(1<<i)
                    if t not in seen: seen.add(t); nf.append(t)
        fr=nf
    return seen
if __name__=='__main__':
    for m in ['iso','rt']:
        print(m,[len(reach(m,n)) for n in range(1,5)])
