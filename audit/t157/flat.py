#!/usr/bin/env python3
"""agentA's own reader of the vector files. Two-word files: each line = one call.  v2 files: header
'// benchvec words=W mems=M', then hex words (// comments stripped); per-call length = W + sum of array lengths
(given on the command line, from the C, hand-checked).  Prints 'CALL i w...'.
usage: flat.py FILE [ARRAYLEN ...]"""
import re, sys
f, lens = sys.argv[1], [int(x) for x in sys.argv[2:]]
lines = open(f).read().split("\n")
m = re.match(r"// benchvec words=(\d+) mems=(\d+)", lines[0])
if not m:
    calls = [l.split() for l in lines if l.strip()]
    assert all(len(c) == 2 for c in calls), "two-word file expected"
else:
    w, nm = int(m.group(1)), int(m.group(2))
    assert nm == len(lens), f"file has mems={nm}, harness expects {len(lens)}"
    toks = []
    for l in lines[1:]:
        toks += l.split("//")[0].split()
    per = w + sum(lens)
    assert len(toks) % per == 0, f"{len(toks)} words not multiple of {per}"
    calls = [toks[i:i + per] for i in range(0, len(toks), per)]
    nc = sum(1 for l in lines if re.match(r"// call \d+", l))
    if nc and nc != len(calls): sys.exit(f"comment says {nc} calls, words give {len(calls)}")
for i, c in enumerate(calls):
    assert all(re.fullmatch(r"[0-9a-fA-F]{1,8}", t) for t in c)
    print("CALL", i, " ".join(c))
