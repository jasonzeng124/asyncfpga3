import re,sys
F='/root/wt-f7/formal/lean/Formal/Cells/'
import os
F=os.path.expanduser('~/wt-f7/formal/lean/Formal/Cells/')
s=open(F+'ArbPin2.lean').read()
names=dict((int(a),b) for a,b in re.findall(r"`(\d+)` (\w+)[,.]?\n",s))
rows=[]
for m in re.finditer(r"⟨(\d+), (\d+), ⟨([-\d, ]+)⟩, (true|false), (true|false), (true|false), (true|false)⟩",s):
    i,c=int(m.group(1)),int(m.group(2)); B=list(map(int,m.group(3).split(',')))
    rows.append((i,c,dict(zip("a1 A1 a2 A2 l L b1 B1 b2 B2 c5 C5 c6 C6".split(),B)),[m.group(k)=='true' for k in (4,5,6,7)]))
print('rows',len(rows),'arbiters',len(names))
def k(B):
    return dict(k12=B['a1']+B['c6']-B['B1'],k21=B['a2']+B['c5']-B['B2'],
      kO1=min(B['a2']+B['c5']-B['B2'],B['a2']+B['c6']+1-B['B2']),kO2=min(B['a1']+B['c6']-B['B1'],B['a1']+B['c5']+1-B['B1']))
pt=[min(k(B).values()) for i,c,B,v in rows if c<4]
print('point min margin',min(pt))
for i,c,B,v in rows:
    kk=k(B)
    if c in(4,5) and min(kk.values())<0: print('range fail',names[i],c,kk,v)
rs=[min(k(B).values()) for i,c,B,v in rows if c in(4,5) and all(v)]
print('range safe min margin',min(rs))
box=[(names[i],k(B)) for i,c,B,v in rows if c==6]
print('box counts', {key:sum(1 for n,kk in box if kk[key]<0) for key in ['k12','k21','kO1','kO2']})
print('box fully safe',[n for n,kk in box if min(kk.values())>=0])
print('box min-of-4 range',min(min(kk.values()) for n,kk in box),max(min(kk.values()) for n,kk in box))
# verdict consistency (safe <-> margin>=0)
bad=[(names[i],c) for i,c,B,v in rows if [x>=0 for x in k(B).values()]!=v]
print('verdict mismatches',bad)
# cross-check vs OnGcdArbFix point Q records
t=open(F+'OnGcdArbFix.lean').read()
Q={}
for m in re.finditer(r"def g(\w+?)_(FMIN|FMAX|SMIN|SMAX)_(lo|hi) : Q := \{([^}]*)\}",t):
    Q[(m.group(1),m.group(2),m.group(3))]=dict((a,int(b)) for a,b in re.findall(r"(\w+) := (-?\d+)",m.group(4)))
cn=['FMIN','FMAX','SMIN','SMAX']; mism=0; cq=set(); aqs=set(); n=0
for i,c,B,v in rows:
    if c>=4: continue
    for lh,suf in (('lo',''),('hi','')):
        q=Q.get((names[i],cn[c],lh))
        if q is None: print('missing',names[i],cn[c]); mism+=1; continue
        X=B if lh=='lo' else {kk.lower() if kk[0]in'AB' or kk in('L','C5','C6') else kk:vv for kk,vv in B.items()}
        b1=B['b1' if lh=='lo' else 'B1']; b2=B['b2' if lh=='lo' else 'B2']
        c5=B['c5' if lh=='lo' else 'C5']; c6=B['c6' if lh=='lo' else 'C6']
        a1=B['a1' if lh=='lo' else 'A1']; a2=B['a2' if lh=='lo' else 'A2']
        ok = b1==q['drg1']+q['agr1'] and b2==q['drg2']+q['agr2'] and c5-c6==q['agq1']-q['agq2'] and a1-a2==q['drs1']-q['drs2']
        cq.add(c5-q['dqg']-q['agq1']); aqs.add(a1-q['drs1']); n+=1
        if not ok: mism+=1; print('mismatch',names[i],cn[c],lh,B,q)
print('checked',n,'mismatches',mism,'implied cq values',sorted(cq)[:10],'... aq',sorted(aqs)[:10])
