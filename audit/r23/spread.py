# own whole-die region-factor spread per draw (gen.py RegionModel formula, linear 1+sigma*N), grid from the routed JSON
import hashlib, math, json, re, sys
def N(seed,rx,ry):
    h=hashlib.md5(("region:%s:%d:%d"%(seed,rx,ry)).encode()).digest()
    u1=(int.from_bytes(h[:8],"big")+1)/2.0**64; u2=int.from_bytes(h[8:],"big")/2.0**64
    return math.sqrt(-2*math.log(u1))*math.cos(2*math.pi*u2)
cells=next(iter(json.load(open(sys.argv[1]))['modules'].values()))['cells']
regs=set()
for c in cells.values():
    m=re.match(r'[A-Z0-9_]*?_X(\d+)Y(\d+)/',c['attributes'].get('NEXTPNR_BEL','')+'/')
    if m: regs.add((int(m[1])//10,int(m[2])//10))
print("occupied regions",len(regs),"x range",min(r[0] for r in regs),max(r[0] for r in regs),"y range",min(r[1] for r in regs),max(r[1] for r in regs))
for sig in (0.16,0.32):
  for d in (1,2,3,4):
    f=[1+sig*N(str(d),*r) for r in regs]
    print("sigma %.2f draw %d min %.2f max %.2f max/min %.1f  <0.4: %d"%(sig,d,min(f),max(f),max(f)/min(f),sum(x<0.4 for x in f)))
