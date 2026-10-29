import re, itertools, sys
import os; src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),"..","..","Formal","Net","OpsMux.lean")).read()
body=re.search(r"def tbl : List MS := \[(.*?)\]\s*\ndef b2n",src,re.S).group(1)
ents=[]
for m in re.finditer(r"⟨([^⟩]*)⟩",body):
    f=[x.strip() for x in m.group(1).split(',')]
    ents.append(tuple((x=='true') if x in('true','false') else int(x) for x in f))
print(len(ents))
names="xr xa yr ya cr ca s zr za j0 j1".split()
B=[False,True]
bad={}
for e in ents:
    E=dict(zip(names,e[:11]))
    for xr,yr,cr,za,j0,j1,zr,xa,ya,ca,s in itertools.product(B,repeat=11):
        if xr!=E['xr'] and E['xr']!=E['xa']: continue
        if yr!=E['yr'] and E['yr']!=E['ya']: continue
        if cr!=E['cr'] and E['cr']!=E['ca']: continue
        if za!=E['za'] and E['za']==E['zr']: continue
        if j0!=E['j0'] and not (E['xr']==j0 and (E['cr'] and not E['s'])==j0): continue
        if j1!=E['j1'] and not (E['yr']==j1 and (E['cr'] and E['s'])==j1): continue
        if zr!=E['zr'] and zr!=(E['j0'] or E['j1']): continue
        if xa!=E['xa'] and not (E['j0']==xa and E['za']==xa): continue
        if ya!=E['ya'] and not (E['j1']==ya and E['za']==ya): continue
        if ca!=E['ca'] and ca!=E['za']: continue
        if s!=E['s'] and (E['cr'] or E['ca']) and (cr or ca): continue
        for v in B:
            chk=[('j0', E['xr']==v and (E['cr'] and not E['s'])==v and E['j0']!=v, (xr==v and (cr and not s)==v) or j0==v),
                 ('j1', E['yr']==v and (E['cr'] and E['s'])==v and E['j1']!=v, (yr==v and (cr and s)==v) or j1==v),
                 ('zr', (E['j0'] or E['j1'])==v and E['zr']!=v, (j0 or j1)==v or zr==v),
                 ('xa', E['j0']==v and E['za']==v and E['xa']!=v, (j0==v and za==v) or xa==v),
                 ('ya', E['j1']==v and E['za']==v and E['ya']!=v, (j1==v and za==v) or ya==v),
                 ('ca', E['za']==v and E['ca']!=v, za==v or ca==v)]
            for g,pre,post in chk:
                if pre and not post:
                    key=(g,v)
                    if key not in bad: bad[key]=(E,dict(xr=xr,yr=yr,cr=cr,za=za,j0=j0,j1=j1,zr=zr,xa=xa,ya=ya,ca=ca,s=s))
for k,v in bad.items(): print(k, v)
