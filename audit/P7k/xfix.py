import re,sys
K=open(sys.argv[1]).read(); F=open(sys.argv[2]).read()
data={}
for m in re.finditer(r'def v_g(\w+?)_(merge\w+?_uarb\d) : E → Quad\n(.*?)\n\n',K,re.S):
    s,a,body=m.groups()
    data[f'g{s}_{a}']={arc:tuple(int(x) for x in v) for arc,*v in re.findall(r'\| \.(\w+) => \((\d+), (\d+), (\d+), (\d+)\)',body)}
cols={'FMIN':0,'FMAX':1,'SMIN':2,'SMAX':3}
mp={'drg1':['rg1'],'drs1':['rs1'],'agr1':['ag1r'],'aRr1':['aR1'],'agq1':['ag1q'],'drg2':['rg2'],'drs2':['rs2'],'agr2':['ag2r'],'aRr2':['aR2'],'agq2':['ag2'],'dqg':['qgw','pqg']}
n=bad=0
for m in re.finditer(r'def (g\w+?_merge\w+?_uarb\d)_(FMIN|FMAX|SMIN|SMAX)_(lo|hi) : Q := \{(.*?)\}',F):
    name,c,lh,body=m.groups()
    if name not in data: print('missing',name); continue
    for k,v in re.findall(r'(\w+) := (\d+)',body):
        v=int(v); tot=sum(data[name][a][cols[c]] for a in mp[k])
        ok = (v*1000<=tot) if lh=='lo' else (v*1000>=tot)
        ok = ok and abs(v*1000-tot)<1000+ (1000 if k=='dqg' else 0)
        n+=1
        if not ok: bad+=1; print('MISMATCH',name,c,lh,k,v,tot)
print('checked',n,'bad',bad,'arbiters',len(data))
