# Independent check of Formal/Core/Prims/XrayData.lean against prjxray-db SDF.
import re,sys
sdfdir,lean=sys.argv[1],sys.argv[2]
def parse(fn):
    L=open(fn).read().split('\n'); out={}
    ct=inst=None
    for i,l in enumerate(L,1):
        m=re.search(r'CELLTYPE "([^"]+)"',l)
        if m: ct=m.group(1)
        m=re.search(r'INSTANCE (\S+)\)',l)
        if m: inst=m.group(1)
        m=re.search(r'\((IOPATH|INTERCONNECT|SETUP|HOLD|SETUPHOLD|RECOVERY|REMOVAL|WIDTH)\s+(.*?)\s*((?:\([\d.:]*\))+)\s*\)\s*$',l.strip())
        if m:
            trip=re.findall(r'\(([\d.]*)::([\d.]*)\)',m.group(3))
            nums=[round(float(x)*1000) for t in trip for x in t]
            out[i]=(ct,inst,m.group(1),m.group(2),nums,l.strip())
    return out
S={'slicel':parse(sdfdir+'/slicel.sdf'),'slicem':parse(sdfdir+'/slicem.sdf')}
cur=None; n=0; bad=0; lab=0
pinsdf={'cin':'CIN','cyinit':'CYINIT','di0':'DI0','di1':'DI1','di2':'DI2','di3':'DI3','s0':'S0','s1':'S1','s2':'S2','s3':'S3'}
var={'base':'CARRY4','o5':'CARRY4_O5','ax':'CARRY4_AX','axLboth':'CARRY4_AX_LBOTH','axLff':'CARRY4_AX_LFF','bx':'CARRY4_BX','bxLboth':'CARRY4_BX_LBOTH','bxLff':'CARRY4_BX_LFF','cx':'CARRY4_CX','cxLboth':'CARRY4_CX_LBOTH','cxLff':'CARRY4_CX_LFF','dx':'CARRY4_DX','lboth':'CARRY4_LBOTH','lff':'CARRY4_LFF'}
fm={'f7a':'F7AMUX','f7b':'F7BMUX','f8':'F8MUX'}
for l in open(lean):
    m=re.match(r'def (\w+)',l)
    if m: cur=m.group(1)
    m=re.match(r'\s*\| (.*?) => (?:some )?(.*?) -- (slice[lm])\.sdf:([\d,]+)',l)
    if not m: continue
    pat=[p.strip().lstrip('.') for p in m.group(1).split(',')]
    quads=[[int(x) for x in q.split(',')] for q in re.findall(r'⟨\s*(-?\d+\s*,\s*-?\d+\s*,\s*-?\d+\s*,\s*-?\d+)\s*⟩',m.group(2))]
    st=m.group(3); lines=[int(x) for x in m.group(4).split(',')]
    for q,ln in zip(quads,lines):
        n+=1
        rec=S[st].get(ln)
        if rec is None or rec[4]!=q: bad+=1; print('NUM MISMATCH',cur,pat,q,ln,rec)
        # semantic label checks
        ct,inst,kind,args,_,txt=rec
        a=args.split(); ok=True
        site=st.upper()
        if cur=='selmux':
            idx=quads.index(q) if quads.count(q)==1 else lines.index(ln)
            ok= ct=='SELMUX2_1' and inst==f'{site}/{fm[pat[1]]}' and a==[['0','1','S0'][lines.index(ln)],'OUT']
        elif cur=='carry4Arc':
            ok= ct==var[pat[1]] and inst==site and kind=='IOPATH' and a==[pinsdf[pat[2]],pat[3].upper()]
        elif cur in('lut6Arc','lut5Arc'):
            k='6' if cur=='lut6Arc' else '5'
            ok= ct in ('LUT'+k,'LUT_OR_MEM'+k+'LRAM') and inst.endswith(f'/{pat[1]}{k}LUT') and a==[f'A{int(pat[2])+1}','O'+k]
        elif cur=='f7Hop':
            mx='F7AMUX' if pat[1] in 'AB' else 'F7BMUX'
            ok= inst==f'{site}/{mx}' and a==[pat[1].lower()+'6lut',mx.lower()]
        elif cur=='f8SelHop':
            ok= inst==f'{site}/F8MUX' and a==['bx','f8mux']
        elif cur in('outMux','outMuxL'):
            L=pat[1]; suf='MUX' if cur=='outMux' else 'MUXL'
            src={'ff5':L.lower()+'5ff','lut5':L.lower()+'5lut','lut6':L.lower()+'6lut','o5':'o5','o6':'o6','cyO':'carry4_o'+str('ABCD'.index(L)),'cyCO':'carry4_co'+str('ABCD'.index(L)),'fmux':{'A':'f7amux','B':'f8mux','C':'f7bmux'}.get(L),'a6lut':'a6lut'}[pat[2]]
            ok= ct=='ROUTING_BEL' and inst==f'{site}/{L}{suf}' and a==[src,(L+suf).lower()]
        elif cur=='carryHop':
            k,L=pat[1].split(); L=L.lstrip('.')
            i='ABCD'.index(L)
            if k=='cy0': ok= inst==f'{site}/{L}CY0' and a[1]=='di'+str(i) if len(a)>1 else False
            else:
                s={'lut5':L.lower()+'5lut','lut6':L.lower()+'6lut','x':L.lower()+'x'}[k]
                ok= inst==f'{site}/CARRY4' and a[0]==s
        else: ok=None
        if ok is not True: lab+=1; print('LABEL?',cur,pat,ln,ct,inst,txt)
print('checked',n,'numeric mismatches',bad,'label issues',lab)
