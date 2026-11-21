import sys,pickle; sys.path.insert(0,"/tmp/claude-0/arbh")
from classify import load
C=load(); nm=C["names"]; idn={x:i for i,x in enumerate(nm)}
H=pickle.load(open(sys.argv[1],"rb")); h=H["hist"]
print("R",H["R"],"res",H["res"])
for x in sys.argv[2:]:
    n=idn[x]; b,ts=h.get(n,(False,[]))
    print("%-18s v0=%d %s"%(x,b,[t for t in ts if t>=H["R"]-1][:12]), "(pre-R flips %d)"%len([t for t in ts if t<H["R"]-1]))
