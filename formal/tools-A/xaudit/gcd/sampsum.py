import json,glob,collections,sys,re
st=[l.rstrip('\n').split('\t') for l in open('/tmp/gcdx/storage_nets.tsv')]
ctl=[n for c,n in st if '.lat.' not in c]; dat=[n for c,n in st if '.lat.' in c]
for f in sys.argv[1:]:
    L=open(f).read().split('\n'); L=[l for l in L if l]
    res=collections.Counter(re.sub(r'rig_res_data=','',' '.join(l.split('res [')[1].split(']')[0].split())) for l in L)
    ok=collections.Counter(l.split('ok_rises ')[1].split()[0] for l in L); er=collections.Counter(l.split('err_rises ')[1].split()[0] for l in L)
    t=[int(l.split('lap1 ')[1].split('ps')[0]) for l in L]
    print(f.split('/')[-1], len(L),'samples; results',dict(res),'ok rises',dict(ok),'err rises',dict(er),'lap1 %d..%d ps'%(min(t),max(t)))
