import csv, sys, statistics
def load(p):
    out = {}
    for r in csv.DictReader(open(p), delimiter='\t'):
        if r['arb'] and r.get('ua_pin') and not r['ua_pin'].startswith('ERR'):
            out[(r['seed'], f"{r['arb']}#{r['k']}")] = r
    return out
M, N = load('rulej_x.tsv'), load('rulej_x_nomux.tsv')
T = {}
for s in 'd234':
    for r in csv.DictReader(open(f'theirs/compare2_{s}.tsv'), delimiter='\t'):
        if r['rule'] == 'J': T[(s, r['row'], r['flavour'])] = r
print("seed row                         | theirs Jx f/s/fG/sG (J0)         | mine-noMUX x f/s/fG/sG         | mine x f/s/fG/sG  mix | mine0 fG/sG")
dif = []
for key in sorted(M):
    s, row = key
    t = T.get((s, row, 'Jx'))
    t = t if t and t['tc_fast'] not in ('-', '') else None
    t0 = T.get((s, row, 'J0'))
    m, n = M[key], N[key]
    th = f"{t['tc_fast']}/{t['tc_slow']}/{t['tc_fastG']}/{t['tc_slowG']}" if t else "-"
    if t and t['tc_fast'] not in ('-', ''): dif.append((int(n['fastx']) - int(t['tc_fast']), int(n['slowx']) - int(t['tc_slow'])))
    flag = ' <-- theirs FAIL' if t and (int(t['tc_fastG']) < 0 or int(t['tc_slowG']) < 0) else ''
    flag += ' <-- mine FAIL' if (int(m['fastGx']) < 0 or int(m['slowGx']) < 0) else ''
    print(f"{s:3} {row.replace('urig.udut.',''):28} | {th:24} | {n['fastx']}/{n['slowx']}/{n['fastGx']}/{n['slowGx']:6} | {m['fastx']}/{m['slowx']}/{m['fastGx']}/{m['slowGx']} {m['mixx']:>5} | {m['fastG0']}/{m['slowG0']}{flag}")
if dif:
    print("noMUX-mine minus theirs (fast, slow): mean", statistics.mean(a for a, b in dif), statistics.mean(b for a, b in dif),
          "median", statistics.median(a for a, b in dif), statistics.median(b for a, b in dif), "n", len(dif))
    print("  |diff|<=15ps:", sum(1 for a, b in dif if abs(a) <= 15 and abs(b) <= 15), "of", len(dif))
# over-credit
for tag in ('d', '2', '3', '4', 'bq2', 'bq3'):
    for nm, D in (('mine', M), ('noMUX', N)):
        xs = [int(r['c_proj']) - int(r['c_x']) for k, r in D.items() if k[0] == tag]
        print(f"overcredit {tag:3} {nm:5}: n {len(xs)} mean {statistics.mean(xs):.0f} max {max(xs)} min {min(xs)} rows c_proj<c_x {sum(1 for x in xs if x < 0)}")
