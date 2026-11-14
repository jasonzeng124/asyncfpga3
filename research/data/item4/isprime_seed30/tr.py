# usage: tr.py WORK BELTSV t0 t1 netname...   -> transitions of design nets (by driver bel pin) in WORK/win.vcd
import sys,re,collections
work,beltsv,t0,t1=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4]); names=sys.argv[5:]
drv={}
for l in open(beltsv):
    bel,cn,ty,conns=l.rstrip("\n").split("\t")
    for kv in conns.split():
        p,n=kv.split("=",1)
        if p.startswith("O") or p in("Q","CO","O","P") or re.match(r"(O\d|Q|CO\d|P\d+|O5|O6|AMUX|BMUX|CMUX|DMUX)$",p):
            drv.setdefault(n,"%s/%s"%(bel,p))
# bel/pin keys in nets.map
n2pin={};pin2n={};alias={}
for l in open(work+"/nets.map"):
    if l.startswith("#"):continue
    a,b=l.split(None,1);b=b.strip()
    if "/" in b and b.startswith(("SLICE","DSP","IOB","BUFG","RAMB")): pin2n[b]=a
    else: alias.setdefault(b,a)
want={}
for nm in names:
    nid=alias.get(nm)
    if nid is None:
        d=drv.get(nm)
        if d: nid=pin2n.get(d)
    if nid is None: print("??",nm,drv.get(nm));continue
    want[nid]=nm
codes={}
f=open(work+"/win.vcd")
scope=[]
for l in f:
    if l.startswith("$scope"): scope.append(l.split()[2])
    elif l.startswith("$upscope"): scope.pop()
    elif l.startswith("$var"):
        p=l.split(); 
        if scope==["tb","dut"] and p[4] in want: codes.setdefault(p[3],[]).append(p[4])
    elif l.startswith("$enddefinitions"): break
t=0;ev=[]
for l in f:
    if l[0]=="#":
        t=int(l[1:]); 
        if t>t1: break
        continue
    if t<t0: 
        continue
    c=l[1:].strip() if l[0] in "01xz" else None
    if c in codes:
        for nid in codes[c]: ev.append((t,want[nid],l[0]))
for t,n,v in ev: print(t,v,n)
