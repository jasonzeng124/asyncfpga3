#!/usr/bin/env python3
# lutdep.py UNTRIMMED.fasm TRIMMED.fasm: every LUT whose INIT differs; the pins its O6 / O5 read before and after; OK when
# the new function passes exactly one pin it read before, uninverted (a trimmed delay-line entry). Shard A, 2026-11-20.
import sys,re
def inits(f):
    d={}
    for l in open(f):
        m=re.match(r'(\S+\.\wLUT)\.INIT\[(\d+):(\d+)\]\s*=\s*(\d+)\'b([01]+)',l.strip())
        if m:
            site,hi,lo,w,b=m.group(1),int(m.group(2)),int(m.group(3)),int(m.group(4)),m.group(5)
            v=d.get(site,0); v|=int(b,2)<<lo; d[site]=v
        elif re.match(r'\S+\.\wLUT\.INIT',l): print('UNPARSED',l.strip()); 
    return d
def deps(v,n):  # truth table of n inputs (bits idx = input vector)
    return [i for i in range(n) if any(((v>>x)&1)!=((v>>(x^(1<<i)))&1) for x in range(1<<n))]
def desc(v):
    o6=deps(v,6); o5=deps(v&0xffffffff,5)
    s=f'O6 pins {[f"A{i+1}" for i in o6]}'
    if len(o6)==1:
        i=o6[0]; ident=all(((v>>x)&1)==((x>>i)&1) for x in range(64)); s+=' = '+('A%d'%(i+1) if ident else '~A%d'%(i+1))
    s+=f'; O5 pins {[f"A{i+1}" for i in o5]}'
    return s,o6
u,t=inits(sys.argv[1]),inits(sys.argv[2])
bad=0
for site in sorted(set(u)|set(t)):
    if u.get(site)!=t.get(site):
        su,ou=desc(u.get(site,0)); st,ot=desc(t.get(site,0))
        one = len(ot)==1 and 'A%d'%(ot[0]+1) in st.split('=')[1].split(';')[0] and '~' not in st.split(';')[0]
        # fast-fall / fast-rise / gated lines: the entry passes one of the two pins it read; BD_SYMTRIM symmetric lines
        # (2026-11-20): the element passed the chain pin only (INIT 1010) and the entry passes the other, connected pin
        # (the line input; check 3 confirms it is the side net)
        sym = one and len(ou)==1 and ot != ou
        ok = one and (set(ot)<set(ou) or sym)
        bad+= not ok
        print(site, '\n   before:', su, f'(INIT {u.get(site,0):016x})', '\n   after: ', st, f'(INIT {t.get(site,0):016x})', '\n   ', ('OK: passes one input it read before' if not sym else 'OK: symmetric-line entry (passes the other pin)') if ok else 'CHECK')
print('changed LUTs:', sum(u.get(s)!=t.get(s) for s in set(u)|set(t)), 'not as expected:', bad)
