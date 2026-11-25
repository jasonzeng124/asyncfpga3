"""Bitmask model of the bdc loop ring (mux -> N links -> steer -> mux) for the Lean certificate.
Same semantics as Formal/Net/RingReset.lean (`loopStep`). Prints reachable-set stats and, with
--lean, the state lists as Lean defs."""
import sys
C2N=0x00B200B200B200B2; C2=0x00E800E800E800E8; MJ0=0x0000AE080000AE08; MJ1=0x0000EA800000EA80
STEER=0x8888888822222222; OR2=0xE; SRC=0x1
def lut(init,pins): return (init >> sum(int(bool(p))<<k for k,p in enumerate(pins))) & 1 == 1
def model(N, EXIT):
    J0,J1,ZQ,XA,YA,CQ,R1,R0,A0,SA,XQ,SM,CNT,SS,EX=[N+k for k in range(15)]
    b=lambda s,k:(s>>k)&1==1
    def gates(s):
        out=[]
        for i in range(N):
            a = b(s,ZQ) if i==0 else b(s,i-1)
            bb = b(s,SA) if i==N-1 else b(s,i+1)
            out.append((i, lut(C2N,[a,bb,b(s,i),0,0,0])))
        out += [(J0, lut(MJ0,[b(s,XQ),b(s,CQ),b(s,SM),b(s,J0),0,0])),
                (J1, lut(MJ1,[b(s,R1),b(s,CQ),b(s,SM),b(s,J1),0,0])),
                (ZQ, lut(OR2,[b(s,J0),b(s,J1)])),
                (XA, lut(C2,[b(s,J0),b(s,0),b(s,XA),0,0,0])),
                (YA, lut(C2,[b(s,J1),b(s,0),b(s,YA),0,0,0])),
                (CQ, lut(SRC,[b(s,0)])),
                (R1, lut(STEER,[b(s,N-1),b(s,SS),0,0,0,1])),
                (R0, lut(STEER&0xFFFFFFFF,[b(s,N-1),b(s,SS),0,0,0])),
                (A0, b(s,R0)),
                (SA, lut(OR2,[b(s,A0),b(s,YA)]))]
        return [g for g,v in out if v != b(s,g)]
    def env(s):
        out=[]
        idle = not any(b(s,k) for k in (J0,J1,ZQ,XA,YA))
        if not b(s,XQ) and not b(s,XA) and not b(s,CNT) and not b(s,SM): out.append(s|1<<XQ|1<<CNT)
        if b(s,XQ) and b(s,XA): out.append(s & ~(1<<XQ))
        if b(s,CNT) and not b(s,XQ) and not b(s,SM) and idle: out.append(s|1<<SM)
        if EXIT and b(s,SM) and b(s,SS) and not b(s,EX) and not any(b(s,k) for k in (N-1,R1,R0,A0,SA)):
            out.append((s & ~(1<<SS))|1<<EX)
        return out
    s0 = 1<<SS
    return s0,gates,env
def explore(N,EXIT):
    s0,gates,env=model(N,EXIT)
    seen={s0}; st=[s0]
    while st:
        s=st.pop()
        for t in [s^(1<<g) for g in gates(s)]+env(s):
            if t not in seen: seen.add(t); st.append(t)
    return s0,sorted(seen),gates,env
if __name__=="__main__":
    EXIT = "--exit" in sys.argv
    for N in range(1,6):
        s0,S,gates,env=explore(N,EXIT)
        dead=[s for s in S if not gates(s) and not env(s)]
        D=lambda s: sum(1 for i in range(N) if ((s>>i)&1)!=((s>>((i-1)%N))&1))
        print(N,len(S),"dead",len(dead),"D",sorted({D(s) for s in S}))
