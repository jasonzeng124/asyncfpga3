"""Replay an explorer path in 8z2's independent gate encoding (persim.gates2) with 8t's data
functions (transparent link latches); check every fired gate is excited, and that the final
state has no excited gate except start's LUT (which has offered once)."""
import sys, os, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import explore as X
sys.path.insert(0, os.path.join(X.ROOT, "formal", "lean", "Wip", "C8z2"))
import persim as P
from sim import ev, jval, sel2, selD, outs_of, NINT

def replay(names, ops, out0, a, b, keys):
    NC=len(names); prod={}
    for n,o in enumerate(ops):
        for c in outs_of(o): prod[c]=n
    class S: pass
    s=S(); s.req=[False]*NC; s.ack=[False]*NC
    s.it={n:[False]*NINT.get(o["k"],0) for n,o in enumerate(ops)}
    latch={o["o"]:0 for o in ops if o["k"]=="link"}
    srcv=lambda w: a if w==0 else (b if w==1 else 0)
    def dats():
        memo={}
        def d(c):
            if c in memo: return memo[c]
            o=ops[prod[c]]; k=o["k"]
            if k in("forkG","forkH"): v=d(o["i"])
            elif k=="join": v=ev(o["e"],[jval(j,[d(i) for i in o["ins"]]) for j in o["js"]])
            elif k=="bjoin":
                vs=[d(i) for i in o["ins"]]; v=2*ev(o["ed"],vs)+ev(o["ec"],vs)%2
            elif k=="steerC": v=0
            elif k=="steerD": v=ev(o["fd"],[d(o["j"])//2])
            elif k=="mux": v=d(o["y"]) if sel2(d(o["c"])) else d(o["x"])
            elif k=="muxn": v=d(o["xs"][selD(d(o["c"]))])
            elif k=="amerge":
                g=s.it[prod[c]]; won=g[1] or s.ack[o["y"]]
                v=2*(d(o["y"]) if won else d(o["x"]))+(1 if won else 0)
            elif k=="link": v=d(o["i"]) if s.it[prod[c]][0] else latch[c]
            elif k=="src": v=srcv(o["which"])
            memo[c]=v; return v
        return [d(c) for c in range(NC)]
    GL={}
    for n,o in enumerate(ops):
        for (key,eT,eF) in P.gates2(n,o): GL[key]=(n,eT,eF)
    def get(key): return s.req[key[1]] if key[0]=="r" else (s.ack[key[1]] if key[0]=="a" else s.it[key[1]][key[2]])
    def put(key,v):
        if key[0]=="r": s.req[key[1]]=v
        elif key[0]=="a": s.ack[key[1]]=v
        else: s.it[key[1]][key[2]]=v
    s.D=dats(); offered=0
    for step,key in enumerate(keys):
        n,eT,eF=GL[key]; cur=get(key)
        ok = eF(s) if cur else eT(s)
        assert ok, ("not excited", step, key)
        if key==("r",2) and not cur:
            offered+=1; assert offered==1
        put(key, not cur)
        for o in ops:
            if o["k"]=="link": latch[o["o"]]=s.D[o["o"]]
        s.D=dats()
        for o in ops:
            if o["k"]=="link": latch[o["o"]]=s.D[o["o"]]
        if key==("a",out0) and cur: return "out0 closed at step %d"%step
    exc=[(key,n) for key,(n,eT,eF) in GL.items() if (eF(s) if get(key) else eT(s))]
    return dict(steps=len(keys), excited=exc, out0=(s.req[out0], s.ack[out0]), start=(s.req[2],s.ack[2]))

if __name__=="__main__":
    names,ops,out0=X.sim.load_net()
    a,b,f=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]
    keys=pickle.load(open(f,"rb"))["keys"]
    print(replay(names,ops,out0,a,b,keys))
