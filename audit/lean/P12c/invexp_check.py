# independent numeric check of InvolutionExp claims (auditor P12c)
import sympy as sp, math
T,Tp,tau,D,w=sp.symbols('T T_p tau Delta w',real=True)
d=lambda X: Tp+tau*sp.log(2-sp.exp(-(X+Tp)/tau))
# involution: -d(-d(T)) == T
print("involution residual:", sp.simplify(sp.expand_log(-d(-d(T))-T,force=True)))
dinf=Tp+tau*sp.log(2)
# paper form equality
paper=dinf+tau*sp.log(1-sp.exp(-(T+dinf)/tau))
import random
for _ in range(3):
    v={T:random.uniform(-0.5,3),Tp:random.uniform(0.1,1),tau:random.uniform(0.2,2)}
    if float((T+dinf).subs(v))>0: print("paper-d", float((paper-d(T)).subs(v)))
bad=lambda X: dinf+tau*sp.log(1-sp.exp(-(X+dinf-Tp)/tau))
for tp,ta in [(0.3,1.0),(0.6,1.0),(0.69,1.0)]:
    v={Tp:tp,tau:ta}
    b0=bad(0).subs(v); print("bad: Tp",tp,"tau ln2",ta*math.log(2),"-bad(-bad(0))=",float(-bad(-b0).subs(v)))
def dl(X,tp,ta): return tp+ta*math.log(2-math.exp(-(X+tp)/ta))
# single pulse cancellation threshold by IDM rule
def pulse_cancel(Dl,tp,ta):
    di=tp+ta*math.log(2); out_rise=di; out_fall=Dl+dl(Dl-di,tp,ta); return out_fall<=out_rise
tp,ta=0.3,1.0
for Dl in [ta*math.log(2)-1e-9, ta*math.log(2)+1e-9]:
    print("pulse",Dl,"cancel",pulse_cancel(Dl,tp,ta))
# OR loop event simulation (own derivation) -> latched or lost, find s* by bisection
def loop(s,tp,ta,maxn=20000):
    di=tp+ta*math.log(2)
    out=[di]  # pending output times of channel (alternating rise/fall)
    # input fall at s
    t=s; o=t+dl(t-out[-1],tp,ta)
    if o<=out[-1]: return 'lost',0
    out.append(o)
    k=0
    # subsequent inputs are the outputs themselves (o=y after s)
    idx=0  # next y transition to feed back
    while k<maxn:
        k+=1
        tin=out[idx]; idx+=1
        last=out[-1]
        o=tin+dl(tin-last,tp,ta)
        if o<=last:
            out.pop();  # cancellation: the pending last output removed
            # now y's final value: number of surviving transitions
            return ('latched' if len(out)%2==1 else 'lost'),k
        out.append(o)
    return 'undecided',k
for tp,ta in [(0.3,1.0),(1.0,0.5),(0.424-0.04*math.log(2),0.04)]:
    lo,hi=1e-9,tp+ta*math.log(2)-1e-12
    r_lo=loop(lo,tp,ta)[0]; r_hi=loop(hi,tp,ta)[0]
    for _ in range(200):
        m=(lo+hi)/2
        if loop(m,tp,ta)[0]==r_lo: lo=m
        else: hi=m
    a=math.exp(tp/ta); x=(math.sqrt(1+8*a)-1)/2
    sstar=tp+ta*math.log(2/x); wstar=ta*math.log(x)
    print(f"Tp={tp:.4f} tau={ta}: small s->{r_lo}, large s->{r_hi}; bisection s*={lo:.12f} closed form {sstar:.12f}; w*={wstar:.6f} check d(-w*)-2w*={dl(-wstar,tp,ta)-2*wstar:.2e}")
