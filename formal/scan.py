#!/usr/bin/env python3
"""Textual second line of defence for check.sh: report sorry/admit/native_decide/
bv_decide/axiom tokens in Lean code, ignoring comments (--, nested /- -/) and strings."""
import re, sys
BAD = re.compile(r'(?<![A-Za-z0-9_.])(sorry|admit|native_decide|bv_decide|axiom)(?![A-Za-z0-9_])')
def strip(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: out.append('\n' if src[i] == '\n' else ' '); i += 1; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"': j += 2 if src[j] == '\\' else 1
            out.append(' ' * (j + 1 - i)); i = j + 1; continue
        out.append(src[i]); i += 1
    return ''.join(out)
bad = 0
for f in sys.argv[1:]:
    for k, line in enumerate(strip(open(f).read()).split('\n'), 1):
        if BAD.search(line): print(f"{f}:{k}: {line.strip()}"); bad = 1
sys.exit(bad)
