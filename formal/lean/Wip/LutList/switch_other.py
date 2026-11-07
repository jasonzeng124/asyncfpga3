# patchOut.py ROOT: files OUTSIDE Formal/Cells that use Prelim names through `open Formal.Cells`
#  - qualify `Formal.Cells.<API name>` -> `Formal.Core.LutList.<name>` (code and comments alike)
#  - `open Formal.Cells` (whole-namespace form, not `open Formal.Cells (..)`) -> `open Formal.Cells Formal.Core.LutList`
#  - import line `import Formal.Cells.Prelim` -> `import Formal.Core.LutList`
import sys,os,re
root=sys.argv[1]
NAMES=r'(K3|lutB|lutK|lutIdx|muxTree|o6B|o5B|o6K|o5K|completions|mux_eq|lutIdx_ofFn|entry_eq_testBit|lutB_ofFn|muxTree_ofFn|muxTree_congr|lutK_ofFn|lutK_ofFn_spec)'
ch=[]
for d,_,fs in os.walk(os.path.join(root,'Formal')):
    if '/Formal/Cells' in d+'/': continue
    for f in fs:
        if not f.endswith('.lean'): continue
        p=os.path.join(d,f); s=open(p).read(); t=s
        if p.endswith('Core/LutList.lean') or p.endswith('Core/Bridge.lean'): continue
        t=t.replace('import Formal.Cells.Prelim\n','import Formal.Core.LutList\n')
        t=re.sub(r'\bFormal\.Cells\.'+NAMES+r'\b',r'Formal.Core.LutList.\1',t)
        # any `open ...` line naming the namespace `Formal.Cells` (not a selective `open X (..)`)
        def aug(m):
            line=m.group(0)
            if '(' in line or 'Formal.Core.LutList' in line: return line
            return re.sub(r' Formal\.Cells(?=[ \n]|$)',' Formal.Cells Formal.Core.LutList',line,count=1)
        t=re.sub(r'^\s*open [^\n]*',aug,t,flags=re.M)
        if t!=s: open(p,'w').write(t); ch.append(os.path.relpath(p,root)[:-5].replace('/','.'))
print(' '.join(sorted(ch)))
