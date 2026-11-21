#!/usr/bin/env python3
"""farm_max_sizes.py BASE.vh OUT.vh REQUEST [REQUEST ...] [--override MACRO=N ...] -- a sizing round from the farm:
the per-cell max of corner_audit's proposals (eval_task's proposal_nom.txt / proposal_worst.txt, i.e. both corners)
over every route of the given farm requests (origin/claude/cluster), as max_sizes.py does for local sizes.vh files.

A route that does not mention a macro keeps BASE's value for it (so the max never drops below what an unmentioned
route was verified at); a route whose proposal header does not say "verify: 0 sized constraint(s) below slack" is
counted and reported, and its proposal still enters the max. Macros only in proposals (lines BASE never named, built at
bdc's RTL default) are added. Every moved line is commented with base, max and the spread over routes.
--override fixes a macro by hand (e.g. select links sized by rule E, which corner_audit never shortens)."""
import re, subprocess, sys, collections
import argparse
ap = argparse.ArgumentParser(); ap.add_argument('base'); ap.add_argument('out'); ap.add_argument('reqs', nargs='+')
ap.add_argument('--override', action='append', default=[])
A = ap.parse_args()
ovr = {k: int(v) for k, v in (o.split('=') for o in A.override)}
base_p, out_p, reqs = A.base, A.out, A.reqs
def show(p):
    r = subprocess.run(['git', 'show', 'origin/claude/cluster:' + p], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
base, order = {}, []
for ln in open(base_p):
    m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
    if m: base[m.group(1)] = int(m.group(2)); order.append(m.group(1))
vals = collections.defaultdict(list); n = 0; unverified = []
for req in reqs:
    for t in range(1, 257):
        for c in ('nom', 'worst'):
            s = show(f'results/{req}/{t}/proposal_{c}.txt')
            if not s or not s.startswith('proposal'): continue
            n += 1
            if 'verify: 0 sized constraint(s) below slack' not in s.splitlines()[0]:
                unverified.append(f'{req}/{t}/{c}: {s.splitlines()[0]}')
            prop = {m.group(1): int(m.group(3)) for m in re.finditer(r'(BD_SZ_\S+)\s+(\d+)\s+->\s+(\d+)', s)}
            for k in set(base) | set(prop):
                v = prop.get(k, base.get(k))
                if v is not None: vals[k].append(v)
out = [f"// per-cell max over {n} corner_audit proposals (both corners) of farm {' '.join(reqs)} "
       f"(research/tools/fifteen/farm_max_sizes.py), base {base_p}"]
moved = 0
for k in order + sorted(set(vals) - set(base)):
    v = ovr.get(k, max(vals[k]) if vals[k] else base[k])
    b = base.get(k)
    note = ''
    if k in ovr: note = f'   // set by hand (--override), base {b}'
    elif b is None: note = f'   // NEW (bdc default before), max over routes {v}, min {min(vals[k])}'
    elif v != b: note = f'   // base {b}, max over routes {v}, min {min(vals[k])}'
    if v != b: moved += 1
    out.append(f"`define {k} {v}{note}")
open(out_p, 'w').write('\n'.join(out) + '\n')
print(f"{n} proposals; {moved} macros moved; {len(unverified)} proposals not verified clean")
for u in unverified[:10]: print('  ', u)
