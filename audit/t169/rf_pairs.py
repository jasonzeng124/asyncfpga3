import re,os,sys,statistics as st
R=sys.argv[1]
def P(s,t):
    f=os.path.join(R,s,str(t),"result.txt")
    if not os.path.exists(f): return None
    l=open(f).readline(); d=dict(re.findall(r"(\w+)=(\S+)",l))
    return (l.split()[0],l.split()[1],d.get("status"),int(d["P"]) if d.get("P","").isdigit() else None,d.get("rule"))
base={}
for t in range(1,8): r=P("nsearch1",t); base[(r[0],r[1])]=r
for t in range(8,19): r=P("nsearch1",t); base[(r[0],r[1])]=r
r=P("norw1r2",7); base[(r[0],r[1])]=r
r=P("norw1r2",9); base[(r[0],r[1])]=r
for t in range(33,45): r=P("ringfuse1",t); base[(r[0],r[1])]=r
diffs={}
for t in range(1,33):
    r=P("ringfuse1",t); b=base.get((r[0],r[1]))
    if not r[3] or not b or not b[3]: print("unpaired",r,b); continue
    if r[2]!="PASS": print("excluded?",r,b)
    diffs.setdefault(r[0],[]).append(((r[3]-b[3])/1000,r[1],r[2]))
allv=[]
for k,v in diffs.items():
    d=[x[0] for x in v]; allv+=[x[0] for x in v if x[2]=="PASS"]
    print(k,"n",len(d),"faster",sum(x<0 for x in d),"median %.2f"%st.median(d), [("%.2f"%x[0],x[1],x[2]) for x in v])
print("all PASS pairs",len(allv),"faster",sum(x<0 for x in allv),"median %.2f"%st.median(allv))
