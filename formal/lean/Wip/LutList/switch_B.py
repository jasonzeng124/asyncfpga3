# patchB.py ROOT: in ROOT/Formal/Cells/*.lean (a COPY), switch from Prelim to Core.LutList:
#  - `import Formal.Cells.Prelim` -> `import Formal.Core.LutList`
#  - after the first `namespace Formal.Cells...` line, insert `open Formal.Core.LutList`
#    (only in files that use a Prelim name), and qualify `Formal.Cells.<prelim name>`.
import sys,os,re
root=sys.argv[1]; d=os.path.join(root,'Formal/Cells')
NAMES=r'(K3|lutB|lutK|lutIdx|muxTree|o6B|o5B|o6K|o5K|completions|mux_eq|lutIdx_ofFn|entry_eq_testBit|lutB_ofFn|muxTree_ofFn|muxTree_congr|lutK_ofFn|lutK_ofFn_spec)'
changed=[]
for f in sorted(os.listdir(d)):
    if not f.endswith('.lean') or f=='Prelim.lean': continue
    p=os.path.join(d,f); s=open(p).read(); t=s
    t=t.replace('import Formal.Cells.Prelim\n','import Formal.Core.LutList\n')
    t=re.sub(r'\bFormal\.Cells\.'+NAMES+r'\b',r'Formal.Core.LutList.\1',t)
    if 'import Formal.' in t:
        # every block `namespace Formal.Cells...` gets the open (opens are scoped to the block)
        t=re.sub(r'^(namespace Formal\.Cells\S*\n)',r'\1open Formal.Core.LutList\n',t,flags=re.M)
    if t!=s: open(p,'w').write(t); changed.append(f)
os.remove(os.path.join(d,'Prelim.lean'))
print(len(changed),'files patched; Prelim.lean removed')
