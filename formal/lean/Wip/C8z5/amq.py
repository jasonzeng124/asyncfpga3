import re
txt=open('/home/user/asyncfpga3/formal/lean/Formal/Net/OpsCM.lean').read()
i=txt.index('def atbl : List AS := [')
j=txt.index('def anxt',i)
ents=re.findall(r'⟨([^⟩]*)⟩',txt[i:j])
T=[]
for e in ents:
    f=[x.strip() for x in e.split(',')]
    T.append(tuple([x=='true' for x in f[:8]]+[int(f[8]),int(f[9])]))
print(len(T))
for (xr,xa,yr,ya,g1,g2,zr,za,dx,dy) in T:
    def quiet():
        for v in (False,True):
            if ((g1 or g2)==v and (not v or (not xa and not ya))) and zr!=v: return False
            if (g1==v and za==v) and xa!=v: return False
            if (g2==v and za==v) and ya!=v: return False
            if ((not v or (xr and not g2 and not za)) and (v or not xr)) and g1!=v: return False
            if ((not v or (yr and not g1 and not za)) and (v or not yr)) and g2!=v: return False
        return True
    if quiet():
        print(dict(xr=xr,xa=xa,yr=yr,ya=ya,g1=g1,g2=g2,zr=zr,za=za,dx=dx,dy=dy))
