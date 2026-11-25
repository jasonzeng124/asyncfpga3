from loopgen import explore
for N in range(1,6):
    s0,S,gates,env=explore(N,True)
    J0,J1,ZQ,XA,YA,CQ,R1,R0,A0,SA,XQ,SM,CNT,SS,EX=[N+k for k in range(15)]
    b=lambda s,k:(s>>k)&1==1
    D=lambda s: sum(1 for i in range(N) if ((s>>i)&1)!=((s>>((i-1)%N))&1))
    p1=all(D(s)==0 for s in S if not b(s,CNT))
    p2={D(s) for s in S if b(s,SM) and not b(s,EX)}
    p3={D(s) for s in S if b(s,EX)}
    live=all(gates(s) for s in S if b(s,SM) and not b(s,EX))
    term=[s for s in S if not gates(s) and not env(s)]
    termok=all(b(s,EX) and D(s)==0 for s in term)
    pers=all(h in gates(s^(1<<g)) for s in S for g in gates(s) for h in gates(s) if h!=g)
    print(N,len(S),"pre-entry D=0:",p1,"looping D:",p2,"after exit D:",p3,"live while looping:",live,"terminal ok:",termok,"persistent:",pers)
