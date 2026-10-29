import re, sys
root = sys.argv[1]
txt = open(root + '/formal/notes/C-gcd_hw-hypotheses.md').read()
sec = txt[txt.index('## 0.'):txt.index('## 1. Token level')]
# pairs: `name` (Dir/File.lean:N) ; and `name` (:N) following a file
ok = bad = 0
for row in sec.split('\n'):
    cur = None
    for m in re.finditer(r'`([^`]+)`\s*\(((?:[A-Za-z]+/)*[A-Za-z0-9]+\.lean)?:?(\d+)', row):
        name, f, ln = m.group(1), m.group(2), int(m.group(3))
        if f: cur = f
        if not cur: continue
        base = root + '/formal/lean/Formal/' + cur
        if cur.startswith('tools/'): base = root + '/formal/' + cur
        try: L = open(base).read().split('\n')
        except Exception as e: print('NOFILE', cur); bad += 1; continue
        short = name.split('.')[-1].strip('*')
        line = L[ln-1] if ln-1 < len(L) else ''
        if short in line: ok += 1
        else:
            # find actual line
            act = [i+1 for i, l in enumerate(L) if re.search(r'(theorem|def|lemma|structure|abbrev)\s+(\S*\.)?' + re.escape(short) + r'\b', l)]
            print('MISMATCH', name, cur, ln, '-> actual', act, '| line:', line.strip()[:80]); bad += 1
print('ok', ok, 'bad', bad)
