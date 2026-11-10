# Shard A (UNTRUSTED): does PlanRPS.IslR hold in a simadv dump at given request-rise times?
# usage: islr_check.py DIR RISE... (DIR has netps.json from tools-B/target/lean2json.py and fast_dump.json from
# simadv_hold.py --dump, corner 0.5, pos 0.5 delays); run from formal/.
import json,re,sys,itertools,os
S=sys.argv[1]
N=json.load(open(S+"/netps.json")); D=json.load(open(os.environ.get("DUMP",S+"/fast_dump.json")))["nodes"]
drv={g["out"]:g for g in N["gates"]}
src=open("lean/Formal/Net/CViewPS/IslandData.lean").read()
mem=set(int(a) for a in re.findall(r'\((\d+), (?:true|false), \[',src)); env={186985,104477}
import os
C=float(os.environ.get("CORNER","0.5")); PP=float(os.environ.get("POS","0.5"))
import math
KAP=os.environ.get("KAPPA"); SLOWN=set(open(os.environ["SLOWFILE"]).read().split()) if os.environ.get("SLOWFILE") else set()
NAMES=N["nodes"]; NIDX={n:i for i,n in enumerate(NAMES)}
SLOW=set(NIDX[n] for n in SLOWN)
for n0 in list(SLOW):   # --slowroutes: the copy chains into slow gates' pins are slow too
    if n0 in drv:
        for u in drv[n0]["ins"]:
            while u in drv and drv[u]["k"]==1 and drv[u]["init"]==2:
                SLOW.add(u); u=drv[u]["ins"][0]
def dm(e, out=None):
    lo=(1-C)*e["fmin"]+C*e["smin"]; hi=(1-C)*e["fmax"]+C*e["smax"]
    if KAP is not None:
        k=float(KAP)
        if out in SLOW: return int(math.floor(hi*(1+k)))
        return int(math.ceil(lo*(1-k)))
    return int(round(lo+PP*(hi-lo)))
def chain(g,i):
    s=dm(g["arcs"][i], g["out"]); n=g["ins"][i]
    while n in drv and drv[n]["k"]==1 and drv[n]["init"]==2:
        s+=dm(drv[n]["arcs"][0], n); n=drv[n]["ins"][0]
    return n,s
def fmn(g,i):
    s=g["arcs"][i]["fmin"]; n=g["ins"][i]
    while n in drv and drv[n]["k"]==1 and drv[n]["init"]==2:
        s+=drv[n]["arcs"][0]["fmin"]; n=drv[n]["ins"][0]
    return s
def flips(n): return D.get(str(n),[None,[]])[1]
def v0(n): return D.get(str(n),[False,[]])[0]
def lowon(n,a,b):
    v=v0(n)
    for f in flips(n):
        if f<=a: v=not v
        elif f<=b: return False
        else: break
    return v is False
def forced(k,init,known):
    xs=[i for i in range(k) if i not in known]
    for comb in itertools.product([0,1],repeat=len(xs)):
        a=0
        for i in range(k):
            b=0 if i in known else comb[xs.index(i)]
            a|=b<<i
        if init>>a&1: return False
    return True
for tr in [int(x) for x in sys.argv[2:]]:
    t=tr-1; bad=[]
    for w in mem:
        g=drv[w]; known=set()
        for j in range(g["k"]):
            n,d=chain(g,j)
            if (n in mem or n in env) and fmn(g,j)>=1 and lowon(n,t-d,t): known.add(j)
        if not forced(g["k"],g["init"],known): bad.append(w)
    print("rise",tr,"members not forced low by low-read member/env pins:",bad)
