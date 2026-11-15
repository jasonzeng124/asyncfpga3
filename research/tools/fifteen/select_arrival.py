#!/usr/bin/env python3
"""select_arrival.py DUMPDIR KERNEL_V -- the select-ARRIVAL race, measured in simulation (PROGRAM "No blanket rules",
2026-11-15 correction after audit T116): a select must not change while the request it gates is high.

  bd_mux   C(x_req, ctl_req . ~s) / C(y_req, ctl_req . s): the window is the mux's output request z_req high;
  bd_steer req0 = req . ~s, req1 = req . s (combinational): the window is the input req high.
A select bit that changes inside a window can steer the token to the wrong branch, or fire the mux on the wrong input.

DUMPDIR: a fullstack_dump.sh run (nets.map, dump.vcd) -- FAST_MIN and vectors that flip the selects (e.g.
research/data/fifteen/vec_collatz_hold.hex).  KERNEL_V: the route's <kernel>_kernel_bench.v.
Per instance: request rises seen, VIOLATIONS (rises whose window contains a select change), and the smallest lead
(request rise - last select change before it; negative = a change inside the window).
"""
import re, sys, collections, bisect

d, kv = sys.argv[1], sys.argv[2]
src = open(kv).read()
par = {}
def find(x):
    while par.get(x, x) != x:
        par[x] = par.get(par[x], par[x]); x = par[x]
    return x
for a, b in re.findall(r'assign\s+(\w+)\s*=\s*(\w+)\s*;', src):
    par[find(a)] = find(b)
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
def net(expr):
    m = re.fullmatch(r'\s*(\w+)(?:\[(\d+)\])?\s*', expr)
    if not m: return None
    ks = byclass.get((find(m.group(1)), m.group(2))) or (byclass.get((find(m.group(1)), None)) if m.group(2) in (None, '0') else None)
    return nm[ks[0]] if ks else None
insts = []
for m in re.finditer(r'\b(bd_mux|bd_steer)\b\s*(?:#\([^;]*?\))?\s*(\w+)\s*\(([^;]*?)\);', src, re.S):
    kind, name, ports = m.groups()
    pr = dict(re.findall(r'\.(\w+)\(([^()]*)\)', ports))
    s = net(pr.get('s', '')); r = net(pr.get('z_req' if kind == 'bd_mux' else 'req', ''))
    if s and r: insts.append((name, kind, s, r))
    else: print(f"# {name}: select or request net not in the dump (s={pr.get('s')}, req net missing={r is None})")
want = {x for _, _, s, r in insts for x in (s, r)}
ids = collections.defaultdict(list); ev = collections.defaultdict(list); t = 0
for l in open(d + '/dump.vcd'):
    if l.startswith('$var'):
        p = l.split()
        if p[4] in want: ids[p[3]].append(p[4])
    elif l[0] == '#': t = int(l[1:])
    elif l[0] in '01xz':
        for x in ids.get(l[1:].strip(), ()): ev[x].append((t, l[0]))
print("instance\tkind\trises\tviolations\tmin_lead_ps")
tot = 0
for name, kind, s, r in insts:
    rises = [t for t, v in ev[r] if v == '1']; falls = [t for t, v in ev[r] if v == '0']
    sch = sorted(t for t, _ in ev[s])
    viol = 0; lead = None
    for x in rises:
        j = bisect.bisect_right(falls, x); f = falls[j] if j < len(falls) else None
        k = bisect.bisect_right(sch, x)
        inside = [c for c in sch[k:] if f is None or c < f]
        if inside:
            viol += 1; l_ = x - inside[0]
        else:
            l_ = x - sch[k - 1] if k else None
        if l_ is not None and (lead is None or l_ < lead): lead = l_
    tot += viol
    print(f"{name}\t{kind}\t{len(rises)}\t{viol}\t{lead if lead is not None else 'NA'}")
print(f"# select-arrival violations: {tot}")
