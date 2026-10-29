#!/usr/bin/env python3
"""Auditor's comment/string-aware keyword scan of Lean files.
Usage: kwgrep.py DIR...  -> prints file:line:keyword for forbidden tokens outside comments/strings."""
import sys, os, re
KW = re.compile(r'(?<![\w.])(sorry|admit|native_decide|implemented_by|extern|unsafe|csimp|axiom|opaque|decide\s*\+native|Lean\.ofReduceBool|ofReduceBool)(?![\w])')
def strip(src):
    out=[]; i=0; n=len(src); depth=0
    while i<n:
        if depth==0 and src.startswith('--',i):
            j=src.find('\n',i); j=n if j<0 else j; out.append(' '*(j-i)); i=j; continue
        if src.startswith('/-',i):
            depth+=1; out.append('  '); i+=2; continue
        if depth>0 and src.startswith('-/',i):
            depth-=1; out.append('  '); i+=2; continue
        if depth>0:
            out.append('\n' if src[i]=='\n' else ' '); i+=1; continue
        if src[i]=='"':
            j=i+1
            while j<n and src[j]!='"':
                j+= 2 if src[j]=='\\' else 1
            seg=src[i:j+1]; out.append(''.join('\n' if c=='\n' else ' ' for c in seg)); i=j+1; continue
        out.append(src[i]); i+=1
    return ''.join(out)
hits=0
for d in sys.argv[1:]:
    for root,_,fs in os.walk(d):
        for f in fs:
            if not f.endswith('.lean'): continue
            p=os.path.join(root,f); s=strip(open(p,encoding='utf-8').read())
            for ln,line in enumerate(s.split('\n'),1):
                for m in KW.finditer(line):
                    # `.opaque` constructor and `opaque` as an identifier after `.` are excluded by lookbehind
                    print(f'{p}:{ln}:{m.group(1)}: {line.strip()[:120]}'); hits+=1
print('HITS',hits)
