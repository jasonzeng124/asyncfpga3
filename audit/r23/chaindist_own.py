# own chain-to-datapath distance: per compute cell (has <p>.uor), Euclidean distance (slice units) between the
# centroid of its chain LUT sites and the centroid of its other placed SLICE sites. Also per-cell max chain-cell distance.
import json,re,sys,statistics as st
cells=next(iter(json.load(open(sys.argv[1]))['modules'].values()))['cells']
S=lambda c:(lambda m:(int(m[1]),int(m[2])) if m else None)(re.match(r'SLICE_X(\d+)Y(\d+)',c['attributes'].get('NEXTPNR_BEL','')))
rc=re.compile(r'^(.+)\.chain\.g\[\d+\]\.u(?:$|\.)')
ch={};
for n,c in cells.items():
    m=rc.match(n)
    if m and S(c): ch.setdefault(m[1],[]).append(S(c))
names=set(cells)
res=[]
for base,pts in ch.items():
    p=base.rpartition('.')[0]
    if p+'.uor' not in names: continue
    dp=[S(c) for n,c in cells.items() if n.startswith(p+'.') and not rc.match(n) and S(c)]
    if not dp: continue
    cen=lambda L:(sum(a for a,_ in L)/len(L),sum(b for _,b in L)/len(L))
    a,b=cen(pts),cen(dp); d=((a[0]-b[0])**2+(a[1]-b[1])**2)**.5 if "--manh" not in sys.argv else abs(a[0]-b[0])+abs(a[1]-b[1])
    res.append((d,base))
res.sort()
d=[x for x,_ in res]
print("n=%d mean %.1f max %.1f (%s) >15: %d"%(len(d),st.mean(d),max(d),res[-1][1],sum(x>15 for x in d)))
for x,b in res[-6:]: print("  %.1f %s"%(x,b))
