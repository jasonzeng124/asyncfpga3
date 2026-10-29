import hashlib, math, sys
def N(seed,rx,ry):
    h=hashlib.md5(("region:%s:%d:%d"%(seed,rx,ry)).encode()).digest()
    u1=(int.from_bytes(h[:8],"big")+1)/2.0**64; u2=int.from_bytes(h[8:],"big")/2.0**64
    return math.sqrt(-2*math.log(u1))*math.cos(2*math.pi*u2)
for k in [(3,2),(3,5),(3,4),(2,5),(3,3)]:
    n=N("1",*k)
    print(k, "N=%.4f"%n, " ".join("s%.3f:lin %.3f logn %.3f"%(s,1+s*n,math.exp(s*n)) for s in (0.16,0.2133,0.32)))
# whole map N for draw 1 over die
allN=[N("1",x,y) for x in range(0,6) for y in range(0,15)]
print("min N over 6x15 regions %.3f max %.3f"%(min(allN),max(allN)))
