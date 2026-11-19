#!/usr/bin/env python3
"""Independent recomputation of the headline table (no code shared with suite_table.py).
usage: mytable.py ROOT  (ROOT=results dir); prints per-kernel summary, duplicates, means."""
import os, re, sys, math, statistics as st
ROOT=sys.argv[1]; RS=sys.argv[2]
ORDER=[("suite3a",None),("suite3b",None),("suite8",None),("suite7",None),("suite6",{"ipow"}),("suite9",None),
       ("suite9r3",None),("norw1",None),("norw1r2",None),("gifast1",None),("nsearch1",None)]
if len(sys.argv)>3 and sys.argv[3]=="drop_norw1_c64s8": DROP={("norw1","collatz64","8")}
else: DROP=set()
allruns={}   # (k,seed) -> list of (suite,task,dict)
for s,only in ORDER:
    d=os.path.join(ROOT,s)
    for t in sorted((x for x in os.listdir(d) if x.isdigit()), key=int):
        f=os.path.join(d,t,"result.txt")
        if not os.path.exists(f): continue
        for l in open(f):
            tok=l.split()
            if len(tok)<3: continue
            k,seed=tok[0],tok[1]
            if only and k not in only: continue
            if (s,k,seed) in DROP: continue
            kv=dict(re.findall(r"(\w+)=(\S+)",l)); kv["status"]=tok[2].split("=")[1]
            allruns.setdefault((k,seed),[]).append((s,t,kv,l.strip()))
# duplicates
print("## duplicates (kernel seed: suite/task -> status P rule draws sdf)")
for (k,seed),v in sorted(allruns.items()):
    if len(v)>1:
        print(k,seed," || ".join("%s/%s %s P=%s rule=%s draws=%s sdf=%s"%(s,t,kv["status"],kv.get("P"),kv.get("rule"),kv.get("draws"),kv.get("sdf")) for s,t,kv,_ in v))
latest={kk:v[-1] for kk,v in allruns.items()}
kernels=[]
for ln in open(os.path.join(RS,"research/tools/suite/kernels.txt")):
    for k in ln.split("#")[0].split():
        if k not in kernels: kernels.append(k)
dyn={}
for p in ("research/data/suite/dynamatic/dynamatic_est.tsv","research/tools/suite/dynamatic_ref.tsv"):
    for l in open(os.path.join(RS,p)):
        if l.startswith("#") or not l.strip(): continue
        f=l.rstrip("\n").split("\t"); dyn[f[0]]=(float(f[1]),f[2])
print("\n## table")
ratios=[]; npass=0; attempted=0
for k in sorted(set(kernels)|{kk for kk,_ in latest}):
    rs=[(seed,)+latest[(kk,seed)] for (kk,seed) in latest if kk==k]
    if not rs: print(k,"NO RESULT"); continue
    attempted+=1
    judged=[r for r in rs if r[3]["status"] in("PASS","FAIL")]
    cl=[r for r in judged if r[3].get("rule")=="clean"]; nc=[r for r in judged if r[3].get("rule")!="clean"]
    def dr(x):
        a=sum(int(r[3]["draws"].split("/")[0]) for r in x); b=sum(int(r[3]["draws"].split("/")[1]) for r in x); return "%d/%d"%(a,b)
    ok=bool(judged) and all(r[3]["status"]=="PASS" for r in judged) and all(r[3]["draws"].split("/")[0]==r[3]["draws"].split("/")[1] for r in judged)
    npass+=ok
    def Ps(x):
        out=[]
        for r in x:
            P=r[3].get("P","NA")
            if P.isdigit() and int(P)%12000!=0: out.append(int(P)/1000)
        return out
    pc,pn=Ps(cl),Ps(nc)
    m=st.median(pc) if pc else None
    ratio=m/dyn[k][0] if (m and k in dyn) else None
    if ok and ratio and k!="isprime": ratios.append((k,ratio,"ESTIMATE" not in dyn[k][1]))
    srcs=",".join(sorted({"%s"%r[1] for r in rs}))
    others=[r for r in rs if r not in judged]
    print("%-18s %s %d+%d/%d draws %s;%s Pclean=%s Pnc=%s dyn=%s ratio=%s src=%s %s"%(k,"PASS" if ok else ("FAIL" if judged else "NOJUDGED"),len(cl),len(nc),len(rs),dr(cl),dr(nc),
        "%.2f(%.2f-%.2f)"%(m,min(pc),max(pc)) if pc else "-", "%.2f(%.2f-%.2f)"%(st.median(pn),min(pn),max(pn)) if pn else "-",
        dyn.get(k,("-",""))[0], "%.2f"%ratio if ratio else "-", srcs, ("unjudged:"+";".join("s%s %s"%(r[0],r[3]['status']) for r in others)) if others else ""))
g=lambda v: math.exp(sum(map(math.log,v))/len(v))
meas=[r for k,r,mm in ratios if mm]
print("\npass %d of %d listed (%d with any result line)"%(npass,len(set(kernels)|{kk for kk,_ in latest}),attempted))
print("gmean measured n=%d %.3f  [%s]"%(len(meas),g(meas),",".join(k for k,r,mm in ratios if mm)))
print("gmean all n=%d %.3f  [%s]"%(len(ratios),g([r for _,r,_ in ratios]),",".join("%s:%.2f"%(k,r) for k,r,_ in ratios)))
