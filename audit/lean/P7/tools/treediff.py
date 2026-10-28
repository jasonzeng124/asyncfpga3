import sys; sys.argv=[sys.argv[0],sys.argv[1]]+[]; 
exec(open('catobj.py').read().split("for h in sys.argv[2:]")[0])
def tree(h,pre=''):
    t,b=get(h); out={}
    i=0
    while i<len(b):
        sp=b.index(b' ',i); nul=b.index(b'\0',sp); mode=b[i:sp].decode(); name=b[sp+1:nul].decode(); sha=b[nul+1:nul+21].hex(); i=nul+21
        if mode.startswith('4'): out.update(tree(sha,pre+name+'/'))
        else: out[pre+name]=sha
    return out
def ctree(c):
    t,b=get(c); return b.split(b'\n')[0].split()[1].decode()
import os
A=tree(ctree(os.environ['A'])); B=tree(ctree(os.environ['B']))
for k in sorted(set(A)|set(B)):
    if A.get(k)!=B.get(k): print(k)
