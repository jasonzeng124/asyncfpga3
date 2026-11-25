# apply_lutlist2.py ROOT [--part A|B|C|all]
#
# Applies the coordinated "delete Formal/Cells/Prelim.lean" patch to a tree ROOT
# (a directory containing Formal/; run it on a COPY or on the real formal/lean when
# the lead makes the one coordinated commit). Probe LutList2 (shard A), 2026-10-28.
# Re-derived from Wip/LutList/switch_{B,C,other}.py with one fix (rule B3 below).
#
#  A  Formal/Core/Bridge.lean   <- Wip/LutList2/Core/Bridge.lean (complete file;
#                                  imports Formal.Core.LutList, not Cells.Prelim/MuxTree)
#  B  Formal/Cells/*.lean
#     B1 `import Formal.Cells.Prelim` -> `import Formal.Core.LutList`
#     B2 `Formal.Cells.<N>` -> `Formal.Core.LutList.<N>` for N in NAMES (code and docs)
#     B3 after EVERY line `namespace Formal.Cells...` insert `open Formal.Core.LutList`,
#        but only in files whose import closure (after B1) reaches Formal.Core.LutList
#        (fix: Wip/LutList/switch_B.py also patched Cells/ConstraintsKappa, which does
#        not import LutList -> "unknown namespace").
#     B4 delete Formal/Cells/Prelim.lean
#  C  Formal/{Net,Gen,Timing}/*.lean
#     C1 the four direct users (Net/CoreLutPrelim, Net/Fasm/Basic, Gen/PrelimSem,
#        Net/Import/PrelimSem): Wip/LutList/switch_C.py rules (code only): import line
#        (CoreLutPrelim: Prelim+MuxTree -> LutList), qualified names, and
#        Fasm/Basic's `o6B`/`o5B` in PLut.fn qualified.
#     C2 every file: B2's renaming; in each whole-namespace `open ... Formal.Cells ...`
#        line add ` Formal.Core.LutList` right after `Formal.Cells`
#        (Wip/LutList/switch_other.py rules).
import sys, os, re, shutil

HERE = os.path.dirname(os.path.abspath(__file__))
NAMES = r'(K3|lutB|lutK|lutIdx|muxTree|o6B|o5B|o6K|o5K|completions|mux_eq|lutIdx_ofFn|entry_eq_testBit|lutB_ofFn|muxTree_ofFn|muxTree_congr|lutK_ofFn|lutK_ofFn_spec)'
root = sys.argv[1]
part = sys.argv[sys.argv.index('--part') + 1] if '--part' in sys.argv else 'all'
F = os.path.join(root, 'Formal')

def rd(p): return open(p).read()
def wr(p, s): open(p, 'w').write(s)
changed = []
def put(p, s):
    if rd(p) != s: wr(p, s); changed.append(os.path.relpath(p, root))

# ---------- A ----------
if part in ('A', 'all'):
    dst = os.path.join(F, 'Core/Bridge.lean')
    new = rd(os.path.join(HERE, 'Core/Bridge.lean'))
    if rd(dst) != new: wr(dst, new); changed.append('Formal/Core/Bridge.lean')

# ---------- B ----------
if part in ('B', 'all'):
    cells = os.path.join(F, 'Cells')
    for f in sorted(os.listdir(cells)):
        if not f.endswith('.lean') or f == 'Prelim.lean': continue
        p = os.path.join(cells, f); s = rd(p)
        t = s.replace('import Formal.Cells.Prelim\n', 'import Formal.Core.LutList\n')
        t = re.sub(r'\bFormal\.Cells\.' + NAMES + r'\b', r'Formal.Core.LutList.\1', t)
        if t != s: wr(p, t)
    # import graph after B1 (whole tree), for B3
    mods = {}
    for d, _, fs in os.walk(F):
        for f in fs:
            if f.endswith('.lean'):
                q = os.path.join(d, f); m = os.path.relpath(q, root)[:-5].replace('/', '.')
                mods[m] = [l.split()[1] for l in open(q) if l.startswith('import ')]
    memo = {}
    def reaches(m):
        if m in memo: return memo[m]
        memo[m] = False
        v = any(i == 'Formal.Core.LutList' or (i in mods and reaches(i)) for i in mods.get(m, []))
        memo[m] = v; return v
    for f in sorted(os.listdir(cells)):
        if not f.endswith('.lean') or f == 'Prelim.lean': continue
        p = os.path.join(cells, f); m = 'Formal.Cells.' + f[:-5]
        if reaches(m):
            s = rd(p)
            t = re.sub(r'^(namespace Formal\.Cells\S*\n)', r'\1open Formal.Core.LutList\n', s, flags=re.M)
            if t != s: wr(p, t)
    pre = os.path.join(cells, 'Prelim.lean')
    if os.path.exists(pre): os.remove(pre); changed.append('Formal/Cells/Prelim.lean (deleted)')

# ---------- C ----------
if part in ('C', 'all'):
    C1 = ['Net/CoreLutPrelim.lean', 'Net/Fasm/Basic.lean', 'Gen/PrelimSem.lean', 'Net/Import/PrelimSem.lean']
    def code(s):
        s = s.replace('import Formal.Cells.Prelim\nimport Formal.Cells.MuxTree\n', 'import Formal.Core.LutList\n')
        s = s.replace('import Formal.Cells.Prelim\n', 'import Formal.Core.LutList\n')
        s = s.replace('Formal.Cells.MuxTree.muxTree_eq_lutK', 'Formal.Core.LutList.muxTree_eq_lutK')
        s = s.replace('Formal.Cells.Prelim', 'Formal.Core.LutList')
        s = re.sub(r'Formal\.Cells\.(K3|lutB|lutK|lutIdx|muxTree|o6B|o5B|o6K|o5K|completions)\b', r'Formal.Core.LutList.\1', s)
        return s
    for rel in C1:
        p = os.path.join(F, rel); s = rd(p)
        parts = re.split(r'(/-[\s\S]*?-/|--[^\n]*)', s)
        t = ''.join(x if i % 2 else code(x) for i, x in enumerate(parts))
        if rel == 'Net/Fasm/Basic.lean':
            t = t.replace('  | .o6, v => o6B L.init v\n  | .o5, v => o5B L.init v\n',
                          '  | .o6, v => Formal.Core.LutList.o6B L.init v\n  | .o5, v => Formal.Core.LutList.o5B L.init v\n')
        if t != s: wr(p, t)
    def aug(mt):
        line = mt.group(0)
        if '(' in line or 'Formal.Core.LutList' in line: return line
        return re.sub(r' Formal\.Cells(?=[ \n]|$)', ' Formal.Cells Formal.Core.LutList', line, count=1)
    for sub in ('Net', 'Gen', 'Timing'):
        for d, _, fs in os.walk(os.path.join(F, sub)):
            for f in fs:
                if not f.endswith('.lean'): continue
                p = os.path.join(d, f); s = rd(p)
                t = s.replace('import Formal.Cells.Prelim\n', 'import Formal.Core.LutList\n')
                t = re.sub(r'\bFormal\.Cells\.' + NAMES + r'\b', r'Formal.Core.LutList.\1', t)
                t = re.sub(r'^\s*open [^\n]*', aug, t, flags=re.M)
                if t != s: wr(p, t)

# report residual uses (should print nothing but doc-comment mentions)
for d, _, fs in os.walk(F):
    for f in fs:
        if f.endswith('.lean'):
            for n, l in enumerate(open(os.path.join(d, f)), 1):
                if l.strip() == 'import Formal.Cells.Prelim' or re.search(r'\bFormal\.Cells\.' + NAMES + r'\b', l):
                    print('residual:', os.path.join(d, f), n, l.rstrip())
print('done, part', part)
