# Shard A (UNTRUSTED): does PlanRPS.IslR hold in a simadv dump at given request-rise times?
# usage: islr_check.py DIR RISE... (DIR has netps.json from tools-B/target/lean2json.py and fast_dump.json from
# simadv_hold.py --dump, corner 0.5, pos 0.5 delays); run from formal/.
import json,re,sys,itertools
S=sys.argv[1]
N=json.load(open(S+"/netps.json")); D=json.load(open(S+"/fast_dump.json"))["nodes"]
drv={g["out"]:g for g in N["gates"]}
src=open("lean/Formal/Net/CViewPS/IslandData.lean").read()
mem=set(int(a) for a in re.findall(r'\((\d+), (?:true|false), \[',src)); env={186985,104477}
dm=lambda e: int(round((0.5*e["fmin"]+0.5*e["smin"])+0.5*((0.5*e["fmax"]+0.5*e["smax"])-(0.5*e["fmin"]+0.5*e["smin"]))))
def chain(g,i):
    s=dm(g["arcs"][i]); n=g["ins"][i]
    while n in drv and drv[n]["k"]==1 and drv[n]["init"]==2:
        s+=dm(drv[n]["arcs"][0]); n=drv[n]["ins"][0]
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
