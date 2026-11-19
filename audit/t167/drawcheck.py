import os,re,sys
R=sys.argv[1]
for s in sorted(os.listdir(R)):
    for t in sorted((x for x in os.listdir(os.path.join(R,s)) if x.isdigit()),key=int):
        d=os.path.join(R,s,t); f=os.path.join(d,"result.txt")
        if not os.path.exists(f) or not open(f).read().strip(): continue
        l=open(f).read().split("\n")[0]; m=re.search(r"draws=(\d+)/(\d+)",l)
        if not m: continue
        dl=[x for x in open(os.path.join(d,"draws.txt")) if x.startswith("draw")] if os.path.exists(os.path.join(d,"draws.txt")) else []
        npass=sum(1 for x in dl if ":: PASS" in x and re.search(r"PASS (\d+)/\1\b",x))
        bad=[x.strip()[:150] for x in dl if not (":: PASS" in x and re.search(r"PASS (\d+)/\1\b",x))]
        if (int(m.group(1)),int(m.group(2)))!=(npass,len(dl)) or bad:
            print(s,t,l.split()[0],l.split()[1],"result",m.group(0),"draws.txt pass %d/%d"%(npass,len(dl)),bad[:3])
