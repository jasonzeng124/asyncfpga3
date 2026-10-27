import csv, glob
M = {}
for f in glob.glob('rulee_*.tsv'):
    for r in csv.DictReader(open(f), delimiter='\t'):
        if r.get('fast') not in (None, ''): M[(r['seed'], r['gate'])] = r
T = {}
for s in 'd234':
    for r in csv.DictReader(open(f'theirs/compare2_{s}.tsv'), delimiter='\t'):
        if r['rule'] == 'E': T[(s, r['row'], r['flavour'])] = r
nsdf = sum(1 for k, m in M.items() if (k[0], k[1], 'E') in T and int(m['sdf_raw']) == int(T[(k[0], k[1], 'E')]['proj_raw']))
print("sdf raw equal to skew's raw:", nsdf, "of", sum(1 for k in M if (k[0], k[1], 'E') in T))
print("seed gate | theirs E fast/slow/fG/sG | theirs E0 fG/sG | mine fast/slow/fG/sG | mix mixG | mine0 fG/sG")
for k in sorted(M):
    m = M[k]; t = T.get((k[0], k[1], 'E')); t0 = T.get((k[0], k[1], 'E0'))
    fail_t = t and (int(t['tc_fastG']) < 0 or int(t['tc_slowG']) < 0)
    fail_t0 = t0 and (int(t0['tc_fastG']) < 0 or int(t0['tc_slowG']) < 0)
    fail_m = int(m['fastG']) < 0 or int(m['slowG']) < 0
    fail_u = int(m['fast']) < 0 or int(m['slow']) < 0
    if fail_t or fail_t0 or fail_m or fail_u:
        th = f"{t['tc_fast']}/{t['tc_slow']}/{t['tc_fastG']}/{t['tc_slowG']}" if t else '-'
        th0 = f"{t0['tc_fastG']}/{t0['tc_slowG']}" if t0 else '-'
        print(f"{k[0]:3} {k[1].replace('urig.udut.',''):12} | {th:22} | {th0:10} | {m['fast']}/{m['slow']}/{m['fastG']}/{m['slowG']} | {m['mix']} {m['mixG']} | {m['fastG0']}/{m['slowG0']}")
for s in ('d', '2', '3', '4', 'bq2', 'bq3'):
    rs = [m for k, m in M.items() if k[0] == s]
    if not rs: continue
    mn = lambda f: min(int(r[f]) for r in rs)
    print(f"{s}: n {len(rs)} min fast {mn('fast')} slow {mn('slow')} fastG {mn('fastG')} slowG {mn('slowG')} mix {mn('mix')} mixG {mn('mixG')}; band fails {sum(1 for r in rs if int(r['fastG'])<0 or int(r['slowG'])<0)}; mix fails {sum(1 for r in rs if int(r['mix'])<0)}; fb_arcs max {max(int(r['fb_arcs']) for r in rs)}")
