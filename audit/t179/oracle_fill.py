#!/usr/bin/env python3
"""T179 own oracle for kernels/fill (from fill.c semantics): reads vec.hex and a GLS log, checks out0 (odata) and the
final a[32] of every call (BENCHMEM lines)."""
import sys, re
M = 0xffffffff
def s32(v): v &= M; return v - (1 << 32) if v >> 31 else v
def fill(a, n, x):
    a = list(a); s = 0; j = 3; x = s32(x)
    for i in range(s32(n)):
        x = s32((x ^ s32(x << 5)) + i); a[j] = x & M; s = s32(s + (x >> 3)); j = (j + 7) & 31
    return a, s & M
calls = []; cur = None
for ln in open(sys.argv[1]):
    ln = ln.strip()
    if ln.startswith('// call'): cur = {'ops': None, 'a': []}; calls.append(cur); continue
    if not ln or ln.startswith('//') or cur is None: continue
    w = [int(t, 16) for t in ln.split()]
    if cur['ops'] is None: cur['ops'] = w
    else: cur['a'] += w
log = open(sys.argv[2]).read()
res = {int(m.group(1)): (int(m.group(2), 16), int(m.group(3), 16), int(m.group(4), 16), int(m.group(5)))
       for m in re.finditer(r'BENCHRES batch=(\d+) .*?op0=(\w+) op1=(\w+) .*?odata=(\w+).*?completed=(\d+)', log)} if False else {}
for m in re.finditer(r'BENCHRES batch=(\d+) .*?op0=(\w+) op1=(\w+) n=\d+ completed=(\d+) .*?odata=(\w+)', log):
    res[int(m.group(1))] = (int(m.group(2), 16), int(m.group(3), 16), int(m.group(5), 16), int(m.group(4)))
mem = {int(m.group(1)): [int(t, 16) for t in m.group(2).split(',')] for m in re.finditer(r'BENCHMEM batch=(\d+) mem=0 n=32 data=(\S+)', log)}
ok = 0
for b, c in enumerate(calls):
    ea, es = fill(c['a'], *c['ops'])
    r = res.get(b); g = mem.get(b)
    good = r is not None and r[0] == c['ops'][0] and r[1] == c['ops'][1] and r[2] == es and g == ea
    ok += good
    print(f"call {b}: ops {c['ops'][0]:08x} {c['ops'][1]:08x} exp out {es:08x} got {r[2] if r else None and 0:} mem {'match' if g == ea else 'DIFF' if g else 'MISSING'} -> {'OK' if good else 'WRONG'}")
print(f"agreement {ok}/{len(calls)}")
