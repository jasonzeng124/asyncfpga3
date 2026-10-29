import os,re,sys
from fractions import Fraction as F
base=sys.argv[1]
def fr(s): return F(s.replace('-','/'))
for seed in sorted(os.listdir(base)):
    d=os.path.join(base,seed)
    if not os.path.isdir(d): continue
    allc=[]
    for f in os.listdir(d):
        m=re.match(r'k([0-9.]+)_([0-9-]+)_([0-9-]+)\.txt$',f)
        if not m: continue
        txt=open(os.path.join(d,f)).read()
        clean=re.search(r'^VERDICT CLEAN',txt,re.M) is not None
        allc.append((float(m.group(1)),fr(m.group(2)),fr(m.group(3)),clean))
    for k in [0,0.02,0.04,0.06,0.08]:
        iv=sorted((a,b) for kk,a,b,c in allc if c and kk>=k-1e-12)
        x=F(0); ok=True; started=False
        # union covers [0,1]? closed intervals
        cur=F(-1)
        for a,b in iv:
            if a<=max(cur,F(0)) or (cur>=a):
                cur=max(cur,b)
            elif cur<a:
                if cur<F(0) and a==0: cur=b
                else: break
        covered = (iv and iv[0][0]==0 and cur>=1)
        # simple robust: sweep
        cur=F(0); progress=True
        while progress and cur<1:
            progress=False
            for a,b in iv:
                if a<=cur<b: cur=b; progress=True
        print(seed,'kappa',k,'covered by clean cells (kappa>=k):',cur>=1, 'reached',cur)
