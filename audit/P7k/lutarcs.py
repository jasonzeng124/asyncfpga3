import re,sys,collections
T='/root/audit-tc/openxc7/share/nextpnr/prjxray-db/zynq7/timings/'
cands=collections.defaultdict(set)
for t in ['CLBLL_L','CLBLL_R','CLBLM_L','CLBLM_R']:
    s=open(T+t+'.sdf').read()
    cells=re.split(r'\(CELL\b',s)
    groups=collections.defaultdict(list)
    for c in cells:
        m=re.search(r'INSTANCE (\w+)/([A-D])(5|6)LUT',c)
        if not m: continue
        site,let,n=m.groups()
        for p,a,b,cc,d in re.findall(r'IOPATH A(\d) O\d \(([\d.]+)::([\d.]+)\)\(([\d.]+)::([\d.]+)\)',c):
            q=tuple(round(float(x)*1000) for x in (a,b,cc,d))
            cands[q].add(f'{t}/{site}/{let}{n}LUT/A{p}')
            groups[(site,n,p)].append(q)
    for (site,n,p),v in groups.items():
        e=(min(x[0] for x in v),max(x[1] for x in v),min(x[2] for x in v),max(x[3] for x in v))
        cands[e].add(f'ENV {t}/{site}/O{n}/A{p}')
src=open(sys.argv[1]).read()
for m in re.finditer(r'def (v_\w+) : E → Quad\n(.*?)\n\n',src,re.S):
    name,body=m.groups()
    for arc,a,b,c,d in re.findall(r'\| \.(\w+) => \((\d+), (\d+), (\d+), (\d+)\)',body):
        if arc not in ('aq','aRq','aR1','aR2','ag1q','ag1r','ag2','ac1','ac2','ag2r'): continue
        q=tuple(int(x)//1000 for x in (a,b,c,d))
        hit=sorted(x for x in cands.get(q,[]) if 'ENV' in x)
        print(name,arc,q, (hit[:3] if hit else sorted(cands.get(q,['NOMATCH']))[:2]))
