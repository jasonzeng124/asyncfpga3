import re,sys,os
root='/root/t185/wr/cloud/fixtures/frontend'
for f in sorted(os.listdir('.')):
    if not f.endswith('.0.v'): continue
    k=f[:-4]; t=open(f'{root}/{k}/comp/handshake_transformed.mlir').read()
    defs={}
    for m in re.finditer(r'^\s*(%[\w]+)(?::\d+)?\s*=\s*(.*)$',t,re.M): defs[m.group(1)]=m.group(2)
    def res(v,depth=0):
        v=v.split('#')[0]; d=defs.get(v,'?')
        m=re.match(r'constant\s.*value\s*=\s*(-?\d+)',d)
        if m: return 'CONST',int(m.group(1))
        m=re.match(r'(fork|extui|extsi|trunci|buffer)\b.*?(%[\w#]+)\s*\{',d)
        if m and depth<10: return res(m.group(2),depth+1)
        return 'VAR',d[:60]
    for m in re.finditer(r'=\s*(shli|shrui|shrsi)\s+(%[\w#]+),\s*(%[\w#]+).*?:\s*<(i\d+)>',t):
        kind,val=res(m.group(3)); w=int(m.group(4)[1:])
        flag='' if kind=='VAR' else ('OK' if 0<=val<w else 'BAD')
        print(k,m.group(1),w,kind,val,flag)
