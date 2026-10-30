# independent recomputation of draw-1 region factors (gen.py RegionModel formula), linear sfactor
import hashlib, math
def N(seed,rx,ry):
    h=hashlib.md5(("region:%s:%d:%d"%(seed,rx,ry)).encode()).digest()
    u1=(int.from_bytes(h[:8],"big")+1)/2.0**64; u2=int.from_bytes(h[8:],"big")/2.0**64
    return math.sqrt(-2*math.log(u1))*math.cos(2*math.pi*u2)
for k in [(1,5),(0,5),(0,6),(0,7)]:
    n=N("1",*k); print(k,"N=%.4f 2x lin %.4f 1x lin %.4f"%(n,1+0.32*n,1+0.16*n))
