#!/usr/bin/env python3
"""ssa_check.py MLIR... -- structural sanity of a handshake MLIR file after a textual rewrite.

Checks: every SSA value defined once; every defined value (each fork / multi-result output) used exactly once
(handshake channels are point to point); every used value defined; `fork [n]` agrees with `%x:n`; handshake.name
unique.  Prints OK or the problems; exit 1 on any problem.  A syntactic check, not a semantic one.
"""
import collections
import re
import sys

OPRE = re.compile(r'^\s*(?P<res>%[\w]+(?::\d+)?(?:\s*,\s*%[\w]+(?::\d+)?)*)\s*=\s*(?P<op>"?[\w.]+"?)\s*(?P<rest>.*)$')
VALRE = re.compile(r'%[\w]+(?:#\d+)?')


def check(path):
    probs = []
    defs = collections.Counter()
    uses = collections.Counter()
    names = collections.Counter()
    argn = 0
    for li, ln in enumerate(open(path), 1):
        if 'handshake.func' in ln:
            for a in re.findall(r'(%arg\d+):', ln):
                defs[a] += 1
            continue
        for nm in re.findall(r'handshake.name = "([^"]+)"', ln):
            names[nm] += 1
        m = OPRE.match(ln)
        body = ln
        if m:
            for r in m.group('res').split(','):
                r = r.strip()
                if ':' in r:
                    b, n = r.split(':')
                    for k in range(int(n)):
                        defs[f'{b}#{k}'] += 1
                    fk = re.match(r'fork \[(\d+)\]', m.group('op') + ' ' + m.group('rest'))
                    if m.group('op') == 'fork' and (not fk or int(fk.group(1)) != int(n)):
                        probs.append(f'line {li}: fork arity mismatch')
                else:
                    defs[r] += 1
            body = m.group('rest')
        for v in VALRE.findall(body):
            uses[v] += 1
    for v, n in defs.items():
        if n != 1:
            probs.append(f'{v} defined {n} times')
        if uses[v] != 1:
            probs.append(f'{v} used {uses[v]} times')
    for v in uses:
        if v not in defs:
            probs.append(f'{v} used but not defined')
    for nm, n in names.items():
        if n != 1:
            probs.append(f'name {nm} appears {n} times')
    return probs


bad = 0
for p in sys.argv[1:]:
    pr = check(p)
    if pr:
        bad += 1
        print(p, 'PROBLEMS:', '; '.join(pr[:10]))
print(f'{len(sys.argv) - 1 - bad} OK, {bad} with problems')
sys.exit(1 if bad else 0)
