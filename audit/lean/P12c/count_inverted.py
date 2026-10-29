import json,sys,lzma
for p in sys.argv[1:]:
    j=json.load(lzma.open(p) if p.endswith('.xz') else open(p))
    inv=[];bad=[]
    for sec in ('cells','arcs'):
        for k,v in j.get(sec,{}).items():
            if not (isinstance(v,list) and len(v)==2 and all(isinstance(x,int) and x>=0 for x in v)): bad.append((sec,k,v))
            elif v[0]>v[1]: inv.append((sec,k,v))
    for f in ('lut','route','feedback','pad_steps'):
        v=j.get(f)
        if v is not None and isinstance(v,list) and len(v)==2 and v[0]>v[1]: inv.append((f,'',v))
    print(p, "cells",len(j.get('cells',{})),"arcs",len(j.get('arcs',{})),"inverted",len(inv),"malformed",len(bad))
    for x in inv[:25]: print("   ",x)
