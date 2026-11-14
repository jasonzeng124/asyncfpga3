#!/usr/bin/env python3
"""hold_trace.py DUMPDIR KERNEL_V -- trace-measured hold at every link / pipe INPUT stage (the stages the hold audit
reports as "not audited" when the sender is not a link; research/data/fifteen/hold_blind_spots_*.txt).

DUMPDIR: a fullstack_dump.sh run (nets.map, dump.vcd).  KERNEL_V: the route's <kernel>_kernel_bench.v.
For each bd_link / bd_pipe instance X of the kernel:
  E  = the input stage's C node: X.c (bd_link) or X.many.r[1] (bd_pipe); the latch is transparent while E is high;
  P  = the moment the stage has passed its token on: X's req_out (bd_link) or X.many.r[2] / req_out (bd_pipe);
  D  = X's data_in bits (resolved through the kernel's assign aliases to the names the decoded netlist keeps).
A token is safe only if D does not change between P's rise and E's fall (after that the latch is closed).
Reported per instance: the number of E-high windows, the number with a D change inside [P rise, E fall] (VIOLATIONS),
and the smallest margin over all windows: (first D change after P rise) - (E fall), negative = D moved while open.
Windows where D does not change before the next E rise count as margin = (next E rise) - (E fall) (lower bound).
"""
import re, sys, collections, bisect

d, kv = sys.argv[1], sys.argv[2]
src = open(kv).read()
# alias classes from `assign a = b;` (whole buses and single bits)
par = {}
def find(x):
    while par.get(x, x) != x:
        par[x] = par.get(par[x], par[x]); x = par[x]
    return x
def union(a, b): par[find(a)] = find(b)
for a, b in re.findall(r'assign\s+(\w+)\s*=\s*(\w+)\s*;', src):
    union(a, b)
nm = {}
for l in open(d + '/nets.map'):
    if l.startswith('#'): continue
    a, b = l.split()[:2]
    nm.setdefault(b, a)
P = 'bridge_i.udut.'
byclass = collections.defaultdict(list)
for k in list(nm):
    m = re.fullmatch(re.escape(P) + r'(\w+?)(\[(\d+)\])?', k)
    if m: byclass[(find(m.group(1)), m.group(3))].append(k)
def bits(bus, w):
    out = []
    for i in range(w):
        ks = byclass.get((find(bus), str(i))) or (byclass.get((find(bus), None)) if w == 1 else None)
        if ks: out.append(nm[ks[0]])
    return out
insts = []
for m in re.finditer(r'(bd_link|bd_pipe)\s*#\(([^;]*?)\)\s*(\w+)\s*\(([^;]*?)\);', src, re.S):
    kind, params, name, ports = m.groups()
    w = int((re.search(r'\.W\((\d+)\)', params) or [0, 1])[1])
    n = int((re.search(r'\.N\((\d+)\)', params) or [0, 1])[1])
    pr = dict(re.findall(r'\.(\w+)\(([^()]*)\)', ports))
    di = pr.get('data_in', '').strip()
    if not re.fullmatch(r'\w+', di): continue           # constant data (1'b0): nothing to hold
    if kind == 'bd_link': E = nm.get(P + name + '.c'); Pn = nm.get(P + pr['req_out'].strip())
    else:
        E = nm.get(P + name + '.many.r[1]')
        Pn = nm.get(P + name + '.many.r[2]') or nm.get(P + pr['req_out'].strip())
    if not (E and Pn): continue
    insts.append((name, kind, n, E, Pn, bits(di, w)))
want = {}
for name, kind, n, E, Pn, D in insts:
    for x in [E, Pn] + D: want.setdefault(x, set()).add(name)
ids = collections.defaultdict(list); ev = collections.defaultdict(list); t = 0
for l in open(d + '/dump.vcd'):
    if l.startswith('$var'):
        p = l.split()
        if p[4] in want: ids[p[3]].append(p[4])
    elif l[0] == '#': t = int(l[1:])
    elif l[0] in '01xz':
        for x in ids.get(l[1:].strip(), ()): ev[x].append((t, l[0]))
print("instance\tkind\tN\tW_seen\twindows\tviolations\tmin_margin_ps")
rows = []
for name, kind, n, E, Pn, D in insts:
    rises = [t for t, v in ev[E] if v == '1']; falls = [t for t, v in ev[E] if v == '0']
    prise = sorted(t for t, v in ev[Pn] if v == '1')
    dch = sorted(t for x in D for t, _ in ev[x])
    win = viol = 0; mm = None
    for r in rises:
        j = bisect.bisect_right(falls, r)
        if j >= len(falls): continue
        f = falls[j]
        k = bisect.bisect_right(prise, r)
        if k >= len(prise) or prise[k] > f: continue    # token not passed on in this window
        pr_ = prise[k]; win += 1
        q = bisect.bisect_right(dch, pr_)
        nxt = rises[bisect.bisect_right(rises, f)] if bisect.bisect_right(rises, f) < len(rises) else None
        first = dch[q] if q < len(dch) else None
        if first is not None and first <= f: viol += 1; m = first - f
        elif first is not None and (nxt is None or first < nxt): m = first - f
        else: m = (nxt - f) if nxt else None
        if m is not None and (mm is None or m < mm): mm = m
    rows.append((mm if mm is not None else 10**9, f"{name}\t{kind}\t{n}\t{len(D)}\t{win}\t{viol}\t{mm if mm is not None else 'NA'}"))
for _, r in sorted(rows): print(r)
