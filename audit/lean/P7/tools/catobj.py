# read-only git object reader (no git binary): python3 catobj.py <gitdir> <hexprefix>...
import sys, os, zlib, struct, glob
G=sys.argv[1]
packs=[]
for idx in glob.glob(G+'/objects/pack/*.idx'):
    d=open(idx,'rb').read(); assert d[:4]==b'\xfftOc'
    fan=struct.unpack('>256I',d[8:8+1024]); n=fan[255]
    sh=d[1032:1032+20*n]; off=1032+24*n
    offs=struct.unpack('>%dI'%n,d[off:off+4*n]); lo=off+4*n
    packs.append((idx[:-4]+'.pack',sh,offs,d,lo,n))
def obj_off(p,i):
    _,sh,offs,d,lo,n=p; o=offs[i]
    if o&0x80000000: o=struct.unpack('>Q',d[lo+8*(o&0x7fffffff):lo+8*(o&0x7fffffff)+8])[0]
    return o
def readpack(pf,o):
    f=open(pf,'rb'); f.seek(o); b=f.read(1); c=b[0]; t=(c>>4)&7; sz=c&15; s=4
    while c&0x80: c=f.read(1)[0]; sz|=(c&0x7f)<<s; s+=7
    if t==6:
        c=f.read(1)[0]; bo=c&0x7f
        while c&0x80: c=f.read(1)[0]; bo=((bo+1)<<7)|(c&0x7f)
        base_t,base=readpack(pf,o-bo); delta=zlib.decompressobj().decompress(f.read(sz*2+4096)); return base_t,apply(base,delta)
    if t==7:
        h=f.read(20).hex(); delta=zlib.decompressobj().decompress(f.read(sz*2+4096)); bt,base=get(h); return bt,apply(base,delta)
    dc=zlib.decompressobj(); out=b''
    while len(out)<sz: out+=dc.decompress(f.read(65536))
    return t,out[:sz]
def apply(base,dl):
    i=0
    def vint():
        nonlocal i; r=0;s=0
        while True:
            c=dl[i]; i+=1; r|=(c&0x7f)<<s; s+=7
            if not c&0x80: return r
    vint(); tsz=vint(); out=bytearray()
    while i<len(dl):
        c=dl[i]; i+=1
        if c&0x80:
            o=0;l=0
            for k in range(4):
                if c&(1<<k): o|=dl[i]<<(8*k); i+=1
            for k in range(3):
                if c&(1<<(4+k)): l|=dl[i]<<(8*k); i+=1
            if l==0: l=0x10000
            out+=base[o:o+l]
        else: out+=dl[i:i+c]; i+=c
    return bytes(out)
def get(h):
    lp=G+'/objects/'+h[:2]+'/'+h[2:]
    if len(h)==40 and os.path.exists(lp):
        r=zlib.decompress(open(lp,'rb').read()); hd,body=r.split(b'\0',1); return {b'commit':1,b'tree':2,b'blob':3}[hd.split()[0]],body
    for d in glob.glob(G+'/objects/'+h[:2]+'/'+h[2:]+'*'):
        return get(h[:2]+os.path.basename(d))
    hb=h
    for p in packs:
        sh=p[1]
        for i in range(p[5]):
            if sh[20*i:20*i+20].hex().startswith(hb):
                return readpack(p[0],obj_off(p,i))
    raise KeyError(h)
for h in sys.argv[2:]:
    t,b=get(h); print('=====',h,'type',t); print(b.decode('utf8','replace'))
