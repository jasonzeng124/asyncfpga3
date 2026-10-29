# audit r14: resolution time and edge count near s* in the RC+comparator loop (ring_rc.py model).
import math
def run(s, TLOOP, tau, dt=0.25, laps=1500):
    Dp = TLOOP - tau*math.log(2); n_d = int(round(Dp/dt)); buf=[0]*n_d
    y=0.0; c=0; edges=0; tlast=0.0; a=math.exp(-dt/tau)
    for k in range(int(laps*TLOOP/dt)):
        t=k*dt; fb=buf[k%n_d]; f = 1 if t < s else fb
        y = f + (y-f)*a; cn = 1 if y > 0.5 else 0
        if cn != c: edges += 1; tlast = t
        c = cn; buf[k%n_d] = c
    return c, edges, tlast
TL=424
for tau in (150, 100):
    lo, hi = 150.0, 300.0
    for _ in range(40):
        m=0.5*(lo+hi); c,_,_=run(m,TL,tau)
        if c==1: hi=m
        else: lo=m
    ss=0.5*(lo+hi); print("tau=%d s*=%.6f (%.4f TLOOP)"%(tau,ss,ss/TL), flush=True)
    pts=[]
    for e in (30, 10, 3, 1, 0.3, 0.1, 0.03, 0.01):
        for sg in (+1,-1):
            c,ed,tl = run(ss+sg*e,TL,tau)
            pts.append((e,tl)); print("  s*%+g: final=%d edges=%d last_edge=%.0f ps"%(sg*e,c,ed,tl), flush=True)
    # slope of last_edge vs ln(1/e) between e=1 and e=0.01
    t1=[t for e,t in pts if e==1]; t2=[t for e,t in pts if e==0.01]
    print("  TAU_eff ~ %.0f ps (from e=1 -> 0.01)" % ((sum(t2)/2 - sum(t1)/2)/math.log(100)), flush=True)
