import json,glob,collections,sys
st=[l.rstrip('\n').split('\t') for l in open('/tmp/gcdx/storage_nets.tsv')]
ctl=[n for c,n in st if '.lat.' not in c]; dat=[n for c,n in st if '.lat.' in c]
for pat in sys.argv[1:]:
    fs=sorted(glob.glob('/tmp/gcdx/'+pat))
    C=[json.load(open(f))['counts'] for f in fs]
    out=[]
    for cls,nets in (('control',ctl),('data',dat)):
        dev=collections.Counter(); worst=[]
        for n in nets:
            vals=[c[n] for c in C]; mode=collections.Counter(vals).most_common(1)[0][0]
            for i,v in enumerate(vals):
                d=abs(v-mode)
                if d: dev[d]+=1
                if d>=2: worst.append((d,n,v,mode,fs[i].split('_')[-1]))
        out.append('%s: deviations from the per-net mode %s%s'%(cls,dict(dev),(' WORST '+str(sorted(worst,reverse=True)[:3])) if worst else ''))
    print(pat, len(fs),'samples;', ' | '.join(out))
