import re, itertools
src=open('/home/user/asyncfpga3/formal/lean/Formal/Net/OpsCM.lean').read()
body=src[src.index('def atbl'):src.index('def anxt')]
st=[tuple(x=='true' for x in m.split(', ')[:8]) for m in re.findall(r'⟨([^⟩]*)⟩',body)]
print(len(st))
bad=0;busyok=True
for e in st:
    xr,xa,yr,ya,g1,g2,zr,za=e
    if zr or za:
        w=g2 or ya
        if not ((yr or ya) if w else (xr or xa)): busyok=False; print('busy fail',e)
    for n in itertools.product([False,True],repeat=8):
        XR,XA,YR,YA,G1,G2,ZR,ZA=n  # order in my enumeration
        if XR!=xr and not (xr==xa): continue
        if YR!=yr and not (yr==ya): continue
        if ZA!=za and not (za!=zr): continue
        if G1!=g1 and not (G1==xr and (not G1 or (not g2 and not za))): continue
        if G2!=g2 and not (G2==yr and (not G2 or (not g1 and not za))): continue
        if G1 and G2: continue
        if ZR!=zr and not (ZR==(g1 or g2)): continue
        if (not zr) and ZR and not ((not xa) and (not ya)): continue
        if XA!=xa and not (g1==XA and za==XA): continue
        if YA!=ya and not (g2==YA and za==YA): continue
        if (zr or za) and (ZR or ZA) and (G2 or YA)!=(g2 or ya): bad+=1; print('stable fail',e,n)
print('busyok',busyok,'stable bad',bad)
