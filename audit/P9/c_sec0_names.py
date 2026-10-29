# P9: extract backticked identifiers from §0 of notes/C-gcd_hw-hypotheses.md, check each
# is declared in formal/lean (theorem/lemma/def/structure/abbrev/inductive), and file:line refs.
import re, sys, os, subprocess
root = sys.argv[1]
txt = open(root + '/formal/notes/C-gcd_hw-hypotheses.md').read()
sec = txt[txt.index('## 0.'):txt.index('## 1. Token level')]
toks = re.findall(r'`([^`]+)`', sec)
names = set()
for t in toks:
    for p in re.split(r'[\s,/()]+', t):
        p = p.strip('*.:')
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", p) and not p.startswith('H_') and '.' not in p[-1:]:
            names.add(p)
# keep plausible Lean decl names: contain '_' or start lowercase-with-dot path, drop pure words
cand = sorted(n for n in names if ('_' in n or '.' in n or n in ('Held','Cell','CellR','CellI','BndG','StartEnv','ArbUnc','Quiet2','WalkOK','Inertial','LutFb','LutSI','TxCover')) and not n.endswith('.v') and not n.endswith('.py') and not n.endswith('.lean') and not n.endswith('.md'))
leanroots = [root + '/formal/lean', root + '/formal/tools']
decl = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|structure|abbrev|inductive|class)\s+([^\s:({\[]+)", re.M)
alld = {}
for lr in leanroots:
    for dp, dn, fn in os.walk(lr):
        if '.lake' in dp: continue
        for f in fn:
            if f.endswith('.lean'):
                s = open(os.path.join(dp, f), errors='ignore').read()
                for m in decl.finditer(s):
                    alld.setdefault(m.group(2).split('.')[-1], []).append(os.path.relpath(os.path.join(dp, f), root))
found = []; missing = []
for n in cand:
    k = n.split('.')[-1]
    (found if k in alld else missing).append(n)
print('candidates', len(cand), 'found', len(found), 'missing', len(missing))
print('MISSING:', missing)
# file:line refs
refs = re.findall(r'(?:\(|`)?([A-Za-z/]+\.lean):(\d+)', sec)
print('file:line refs', len(refs))
