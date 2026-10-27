import re,sys,glob,os
rtl=sys.argv[1]; lc=sys.argv[2]
inst=[]
for f in sorted(glob.glob(rtl+'/*.v')):
    src=open(f).read()
    # strip comments
    s=re.sub(r'//[^\n]*','',src)
    for m in re.finditer(r'(LUT[1-6](?:_2)?)\s*#\(\s*\.INIT\(([^)]*)\)\s*\)\s*(\w+)\s*\((.*?)\)\s*;',s,re.S):
        prim,init,name,ports=m.groups()
        line=src[:src.find(m.group(0)[:30])].count('\n')+1 if False else None
        pm=dict((a,b.strip()) for a,b in re.findall(r'\.(\w+)\s*\(([^()]*(?:\([^()]*\))?[^()]*)\)',ports))
        inst.append((os.path.basename(f),prim,init.strip(),name,pm))
for i in inst: print(i)
print(len(inst))
