#!/usr/bin/env python3
"""la_aggregate.py REQUEST [CORNER] -- line_account.py's per-route tables (eval_task LINE_ACCT=1 on the farm,
origin/claude/cluster:results/REQUEST/T/la_CORNER/lines.tsv) folded into one row per delay line over every route:
how many routes put it on the critical cycle, its length, what sets it (rule / set_by, counted), the margin, the
covered data path split (logic / latch / enable / wire, medians), and the elements the as-routed path and the logic
alone would need. Markdown to stdout, lines on the cycle on most routes first."""
import subprocess, sys, csv, io, statistics as st, collections
req = sys.argv[1]; corner = sys.argv[2] if len(sys.argv) > 2 else 'worst'
def show(p):
    r = subprocess.run(['git', 'show', 'origin/claude/cluster:' + p], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
rows = collections.defaultdict(list); nroutes = 0; periods = []
for t in range(1, 257):
    s = show(f'results/{req}/{t}/la_{corner}/lines.tsv')
    if s is None: continue
    nroutes += 1
    for r in csv.DictReader(io.StringIO(s), delimiter='\t'):
        r['_t'] = t; rows[r['line']].append(r)
def num(v):
    try: return float(v)
    except (TypeError, ValueError): return None
def med(rs, k):
    v = [num(r.get(k)) for r in rs]; v = [x for x in v if x is not None]
    return (st.median(v), min(v), max(v)) if v else None
def fmt(m, scale=1, d=0):
    if not m: return '--'
    a, lo, hi = (x / scale for x in m)
    return f"{a:.{d}f}" if lo == hi else f"{a:.{d}f} ({lo:.{d}f}..{hi:.{d}f})"
out = []
for line, rs in rows.items():
    on = [r for r in rs if (num(r['cyc_R']) or 0) + (num(r['cyc_F']) or 0) > 0]
    setby = collections.Counter(f"{r['rule']} {r['set_by']}".strip() for r in rs)
    oncyc = [((num(r['cyc_R']) or 0) + (num(r['cyc_F']) or 0)) for r in on]
    out.append((len(on), line, rs, on, setby, oncyc))
out.sort(key=lambda x: (-x[0], -(st.median(x[5]) if x[5] else 0)))
print(f"## {req}, corner {corner}: {nroutes} routes\n")
print("| line | routes on cycle | n | ps | on cycle (R+F, ps, median of those) | set by (routes) | margin ps | data logic / latch / enable / wire | n_need | n_logic |")
print("|---|---|---|---|---|---|---|---|---|---|")
for k, line, rs, on, setby, oncyc in out:
    if k == 0 and all((num(r['n']) or 0) == 0 for r in rs): continue
    sb = ', '.join(f"{a} {b}" for a, b in setby.most_common(3))
    dp = ' / '.join(fmt(med(rs, c)) for c in ('logic', 'latch', 'enable', 'wire'))
    print(f"| {line} | {k}/{len(rs)} | {fmt(med(rs,'n'))} | {fmt(med(rs,'D_ps'))} | {fmt((st.median(oncyc), min(oncyc), max(oncyc)) if oncyc else None)} "
          f"| {sb} | {fmt(med(rs,'margin'))} | {dp} | {fmt(med(rs,'n_need'))} | {fmt(med(rs,'n_logic'))} |")
