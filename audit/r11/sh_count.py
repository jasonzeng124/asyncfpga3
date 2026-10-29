# Independent SDF SETUPHOLD census: s-expression tokenizer, no gen.py regex.
import sys, re, collections
txt = open(sys.argv[1]).read()
tok = re.findall(r'\(|\)|"[^"]*"|[^\s()]+', txt)
def parse(i):
    out=[]
    while i < len(tok):
        t=tok[i]
        if t=='(':
            sub,i=parse(i+1); out.append(sub)
        elif t==')': return out,i+1
        else: out.append(t); i+=1
    return out,i
tree,_=parse(0)
root=tree[0]
def trip(l): return [int(x) for x in ''.join(l).split(':')]
cells=[c for c in root if isinstance(c,list) and c and c[0]=='CELL']
flops={}; shl=[]
for c in cells:
    ct=[x for x in c if isinstance(x,list) and x[0]=='CELLTYPE'][0][1].strip('"')
    inst=[x for x in c if isinstance(x,list) and x[0]=='INSTANCE'][0]
    inst=inst[1] if len(inst)>1 else ''
    for tc in [x for x in c if isinstance(x,list) and x[0]=='TIMINGCHECK']:
        for sh in tc[1:]:
            assert sh[0]=='SETUPHOLD'
            d=sh[1][1]; s=trip(sh[3]); h=trip(sh[4])
            shl.append((ct,inst,d,s,h))
    if ct=='SLICE_FFX': flops[inst]=1
print("cells",len(cells),"SLICE_FFX",len(flops))
print("SETUPHOLD lines",len(shl))
neg=[x for x in shl if min(x[3]+x[4])<0]
print("with any negative value",len(neg),"; non-negative",len(shl)-len(neg))
print("neg setup",sum(1 for x in shl if x[3][0]<0),"neg hold",sum(1 for x in shl if x[4][0]<0))
print("celltypes with SH",collections.Counter(x[0] for x in shl))
print("distinct (pin,setup,hold):",collections.Counter((x[2],x[3][0],x[4][0]) for x in shl))
# per-flop coverage
per=collections.defaultdict(list)
for ct,inst,d,s,h in shl: per[inst].append((d,s[0],h[0]))
old_cov=[i for i in flops if any(s>=0 and h>=0 for _,s,h in per[i])]
new_cov=[i for i in flops if per[i]]
print("flops with any SH (new regex)",len(new_cov),"; with >=1 all-nonneg line (old regex)",len(old_cov))
# what TSU/THD each scheme gives
def tsuthd(lst): return (max(s for _,s,_ in lst),max(h for _,_,h in lst)) if lst else None
oldp=collections.Counter(); newp=collections.Counter(); effnew=0; effold=0
for i in flops:
    n=tsuthd(per[i]); o=tsuthd([x for x in per[i] if x[1]>=0 and x[2]>=0])
    newp[n]+=1; oldp[o]+=1
    if n and (n[0]>0 or n[1]>0): effnew+=1
    if o and (o[0]>0 or o[1]>0): effold+=1
print("old TSU/THD dist",dict(oldp)); print("new TSU/THD dist",dict(newp))
print("flops with an active check: old",effold,"new",effnew)
# pin-set classes
print("pin sets",collections.Counter(tuple(sorted(set(d for d,_,_ in per[i]))) for i in flops))
# per-pin masking: max over pins vs per-pin windows
mask=0
for i in flops:
    if not per[i]: continue
    T,H=tsuthd(per[i])
    for d,s,h in per[i]:
        if s>T or h>H: mask+=1
print("per-pin windows exceeding combined max (should be 0):",mask)
