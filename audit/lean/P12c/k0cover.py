import os,re,sys
from fractions import Fraction as F
base=sys.argv[1]
def fr(s): return F(s.replace('-','/'))
for seed in sorted(os.listdir(base)):
    d=os.path.join(base,seed)
    if not os.path.isdir(d): continue
    for k in ['0','0.06']:
        cells=[]
        for f in os.listdir(d):
            m=re.match(r'k'+re.escape(k)+r'_([0-9-]+)_([0-9-]+)\.txt$',f)
            if not m: continue
            txt=open(os.path.join(d,f)).read()
            clean=re.search(r'^VERDICT CLEAN',txt,re.M) is not None
            cells.append((fr(m.group(1)),fr(m.group(2)),clean,f))
        clean=[(a,b) for a,b,c,_ in cells if c]
        # can we reach 1 from 0 through clean cells (chain a == previous b)?
        reach={F(0)}; changed=True
        while changed:
            changed=False
            for a,b in clean:
                if a in reach and b not in reach: reach.add(b); changed=True
        print(seed,'kappa',k,'cells',len(cells),'clean',len(clean),'covered[0,1]:',F(1) in reach)
