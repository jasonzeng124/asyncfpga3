#!/usr/bin/env python3
"""vcdq.py VCD NETSMAP T0 T1 REGEX... : print transitions of nets whose
routed name (via nets.map) or tb name matches any regex, time-ordered."""
import re, sys
vcd, nmap, t0, t1 = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
pats = [re.compile(p) for p in sys.argv[5:]]
names = {}
for line in open(nmap):
    if line.startswith('#'): continue
    p = line.split(None, 1)
    if len(p) == 2: names[p[0]] = p[1].strip()
ids = {}
scope = []
f = open(vcd)
for line in f:
    w = line.split()
    if not w: continue
    if w[0] == '$scope': scope.append(w[2])
    elif w[0] == '$upscope': scope.pop()
    elif w[0] == '$var':
        code, ref = w[3], w[4]
        full = '.'.join(scope + [ref])
        nm = names.get(ref, '') if scope[-1:] == ['dut'] else full
        label = f"{ref}:{nm}" if nm and nm != full else full
        if any(p.search(label) for p in pats):
            ids.setdefault(code, []).append(label)
    elif w[0] == '$enddefinitions': break
t = 0
for line in f:
    line = line.strip()
    if not line: continue
    if line[0] == '#': t = int(line[1:]); continue
    if line[0] in 'bBrR':
        v, code = line[1:].split()
    else:
        v, code = line[0], line[1:]
    if code in ids and t0 <= t <= t1:
        for lab in ids[code]:
            print(f"{t:>9} {v:>3} {lab}")
