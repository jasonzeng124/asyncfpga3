import sys; sys.path.insert(0,"/tmp/claude-0/race")
from classify import load
C=load(); g=C["gates"]; nm=C["names"]; idn={x:i for i,x in enumerate(nm)}
for x in sys.argv[1:]:
    n=idn[x]; G=g.get(n)
    if G is None: print(x,"no gate (env?)", n in C["ENV"]); continue
    kind="LATCH" if n in C["LATCH"] else ("CTRL" if n in C["CTRL"] else ("EXC" if n in C["EXC"] else "comb"))
    print(x, kind, "EXACT" if n in C["EXACT"] else "DATA", "k=%d init=%x"%(G["k"],G["init"]), C["LATCH"].get(n))
    for j,p in enumerate(G["pins"]): print("   pin%d %-20s live=%s win c0=%s c1=%s %s"%(j,nm[p["src"]],p["live"],p["win"][0],p["win"][1], "EX" if p["src"] in C["EXACT"] else ""))
    print("   readers:", [nm[r] for r in C["rd"][n]][:12])
