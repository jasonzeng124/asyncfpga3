import os,re,sys,glob
R=sys.argv[1]; st={}
for f in sorted(glob.glob(R+"/*/*/result.txt")):
    for l in open(f):
        t=l.split()
        if len(t)<3: continue
        s=t[2]; st[s]=st.get(s,0)+1
        rule=re.search(r"rule=(\S+)",l); rule=rule.group(1) if rule else "?"
        d=os.path.dirname(f); dl=open(d+"/draws.txt").read().splitlines() if os.path.exists(d+"/draws.txt") else []
        for x in dl:
            m=re.search(r"runts <150/500/1000 ps (\d+)/(\d+)/(\d+)",x)
            if m and int(m.group(3))>0: print("RUNT<1ns",f.split('/')[-3],f.split('/')[-2],t[0],t[1],rule,t[2],m.group(0))
            if "NO MONITOR" in x: print("NOMON",f.split('/')[-3],f.split('/')[-2],t[0],t[1],rule,x[:80])
print(st)
