# patch.py SRCROOT DSTROOT [--trial]: apply the LutList switch to C's four files.
# --trial: write them as Wip/LutList/trial/<Name>.lean with module names Wip.LutList.trial.*
import sys,os,re
src,dst=sys.argv[1],sys.argv[2]; trial='--trial' in sys.argv
FILES={'Formal/Net/CoreLutPrelim.lean':'CoreLutPrelim','Formal/Net/Fasm/Basic.lean':'FasmBasic',
       'Formal/Gen/PrelimSem.lean':'GenPrelimSem','Formal/Net/Import/PrelimSem.lean':'ImportPrelimSem'}
def common(s):
    # code only: doc/comments are left as they are (one prose edit below)
    parts=re.split(r'(/-[\s\S]*?-/|--[^\n]*)',s)
    return ''.join(p if i%2 else code(p) for i,p in enumerate(parts))
def code(s):
    s=s.replace('import Formal.Cells.Prelim\nimport Formal.Cells.MuxTree\n','import Formal.Core.LutList\n')
    s=s.replace('import Formal.Cells.Prelim\n','import Formal.Core.LutList\n')
    s=s.replace('Formal.Cells.MuxTree.muxTree_eq_lutK','Formal.Core.LutList.muxTree_eq_lutK')
    s=s.replace('Formal.Cells.Prelim','Formal.Core.LutList')
    s=re.sub(r'Formal\.Cells\.(K3|lutB|lutK|lutIdx|muxTree|o6B|o5B|o6K|o5K|completions)\b',r'Formal.Core.LutList.\1',s)
    return s
def fasm(s):
    s=s.replace('  | .o6, v => o6B L.init v\n  | .o5, v => o5B L.init v\n',
                '  | .o6, v => Formal.Core.LutList.o6B L.init v\n  | .o5, v => Formal.Core.LutList.o5B L.init v\n')
    return s
for f,n in FILES.items():
    s=open(os.path.join(src,f)).read(); t=common(s)
    if n=='FasmBasic': t=fasm(t)
    if trial:
        t=t.replace('import Formal.Net.CoreLutPrelim\n','import Wip.LutList.trial.CoreLutPrelim\n')
        out=os.path.join(dst,'Wip/LutList/trial',n+'.lean')
    else: out=os.path.join(dst,f)
    os.makedirs(os.path.dirname(out),exist_ok=True); open(out,'w').write(t)
    print(out)
