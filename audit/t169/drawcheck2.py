import os,re,sys
R=sys.argv[1]; srcs=sys.argv[2:]
n=0
for st in srcs:
    s,t=st.split("/"); d=os.path.join(R,s,t); f=os.path.join(d,"result.txt")
    l=open(f).readline(); m=re.search(r"draws=(\d+)/(\d+)",l)
    if not m: continue
    dl=[x for x in open(os.path.join(d,"draws.txt")) if x.startswith("draw")] if os.path.exists(os.path.join(d,"draws.txt")) else []
    ok=sum(1 for x in dl if ":: PASS" in x and re.search(r"PASS (\d+)/\1\b",x))
    n+=1
    if (int(m.group(1)),int(m.group(2)))!=(ok,len(dl)): print("MISMATCH",st,l.split()[:2],m.group(0),"draws.txt %d/%d"%(ok,len(dl)))
print("checked",n)
