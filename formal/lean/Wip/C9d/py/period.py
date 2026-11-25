"""Ring of N bd_c2n stages, one token (reset K=1). (1) synchronous unit delay: rise-to-rise gaps of
stage 0. (2) random per-event delays in [dmin,dmax] (inertial, event-driven): min and max
rise-to-rise gap after warm-up, against dmin*p and dmax*p, p = N (N>=4), 6 (N=3)."""
import random, heapq, sys
def ctl(a,b,q): return True if (a and not b) else (False if (not a and b) else q)
def unit(N, T=200):
    s=[i<1 for i in range(N)]; rises=[]
    for t in range(T):
        ns=[ctl(s[i-1], s[(i+1)%N], s[i]) for i in range(N)]
        if ns[0] and not s[0]: rises.append(t+1)
        s=ns
    g=[b-a for a,b in zip(rises,rises[1:])]
    return sorted(set(g[5:]))
def rnd(N, dmin, dmax, T=200000, seed=0):
    R=random.Random(seed); s=[i<1 for i in range(N)]; t=0
    sched={}  # stage -> fire time (excitation persistent)
    def exc(i): return ctl(s[i-1], s[(i+1)%N], s[i]) != s[i]
    for i in range(N):
        if exc(i): sched[i]=t+R.randint(dmin,dmax)
    rises=[]
    while t<T:
        i=min(sched,key=sched.get); t=sched.pop(i); s[i]=not s[i]
        if i==0 and s[0]: rises.append(t)
        for j in (i-1)%N, i, (i+1)%N:
            if exc(j) and j not in sched: sched[j]=t+R.randint(dmin,dmax)
            if not exc(j) and j in sched: raise SystemExit("persistence violated")
    g=[b-a for a,b in zip(rises,rises[1:])][10:]
    return min(g), max(g), sum(g)/len(g)
for N in range(3,9):
    p = 6 if N==3 else N
    mn,mx,av = rnd(N,10,30)
    mn2,mx2,av2 = rnd(N,20,20,seed=1)
    print(f"N={N} unit gaps {unit(N)} | rand[10,30]: min {mn} max {mx} avg {av:.1f}  (p*dmin={p*10}, p*dmax={p*30}, 2N*dmax={2*N*30}) | fixed 20: {mn2},{mx2}")
