#!/usr/bin/env python3
"""farm_pair.py A B ITERS -- latency of farm request A against request B, paired by seed (same seed = the same
placer seed; the routes differ when the netlists differ). eval.txt's `latency latmin=` is in 12 ns cycles over the
itercost vector, so the per-iteration delta is (A - B) * 12 / ITERS ns (xorshift 256, collatz / collatz64 261,
ipow 31). Also: per request, routes whose gate passed at all three corners, and rule E / A rows below 0 (both
corners, report_rows_*.txt)."""
import subprocess, re, sys, statistics as st
A, B, IT = sys.argv[1], sys.argv[2], float(sys.argv[3])
def show(p):
    r = subprocess.run(['git', 'show', 'origin/claude/cluster:' + p], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
def lat(req):
    d = {}
    for t in range(1, 257):
        e = show(f'results/{req}/{t}/eval.txt')
        if not e: continue
        m = re.search(r'latmin=(\d+)', e)
        g = re.findall(r'^gate (\w+) (PASS|FAIL)', e, re.M)
        rows = {}
        for c in ('nom', 'worst'):
            for ln in (show(f'results/{req}/{t}/report_rows_{c}.txt') or '').splitlines():
                f = ln.split()
                if len(f) > 3 and f[0] in ('A', 'E') and f[1].lstrip('-').isdigit() and int(f[1]) < 0:
                    inst = f[2] if 'udut' in f[2] else f[3]
                    k = (f[0], inst.replace('bridge_i.udut.', ''))
                    rows[k] = min(rows.get(k, 0), int(f[1]))
        d[t] = (int(m.group(1)) if m else None, g, rows)
    return d
a, b = lat(A), lat(B)
for name, d in ((A, a), (B, b)):
    gp = sum(1 for v in d.values() if len(v[1]) == 3 and all(x[1] == 'PASS' for x in v[1]))
    gn = sum(1 for v in d.values() if v[1])
    er = [t for t, v in d.items() if any(k[0] == 'E' for k in v[2])]
    worst = {}
    for v in d.values():
        for k, x in v[2].items(): worst[k] = min(worst.get(k, 0), x)
    print(f"{name}: {len(d)} routes; gate 3/3 PASS on {gp}/{gn} gated; E < 0 on {len(er)} routes {er}; worst rows {dict(sorted(worst.items()))}")
ds = [(a[t][0] - b[t][0]) * 12.0 / IT for t in a if t in b and a[t][0] and b[t][0]]
if ds:
    print(f"{A} - {B}: {len(ds)} paired seeds, ns per iteration median {st.median(ds):+.2f} mean {st.mean(ds):+.2f} "
          f"range {min(ds):+.2f}..{max(ds):+.2f}, faster on {sum(1 for x in ds if x < 0)}/{len(ds)}")
