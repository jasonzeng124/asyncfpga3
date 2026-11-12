# T65: recompute research's paired ratios from raw results.tsv (own code). ratio = cyc(base)/cyc(cand), paired by seed+col,
# only PASS rows; prints per-column mean and range and the number of pairs.
import sys, csv, statistics as st
def rd(path, cfg, cyccol):
    d = {}
    for r in csv.DictReader((l for l in open(path) if not l.startswith('#')), delimiter='\t'):
        if r['cfg'] != cfg: continue
        d[(r['seed'], r['col'])] = (r['verdict'], int(r[cyccol]) if r[cyccol].isdigit() else None, r['equiv'])
    return d
cand_f, cand_cfg, base_f, base_cfg, cyccol = sys.argv[1:6]
c, b = rd(cand_f, cand_cfg, cyccol), rd(base_f, base_cfg, cyccol)
print(f"cand {cand_f.split('/')[-2]}:{cand_cfg} rows {len(c)} PASS {sum(v[0].startswith('PASS') for v in c.values())}; base {base_f.split('/')[-2]}:{base_cfg} rows {len(b)}")
for col in ('max', 'min', 'worst'):
    rs = [(s, b[(s, col)][1] / c[(s, col)][1]) for (s, cc) in sorted(c) if cc == col and (s, col) in b
          and c[(s, col)][0].startswith('PASS') and b[(s, col)][0].startswith('PASS') and c[(s,col)][1] and b[(s,col)][1]]
    if rs: print(f"  {col}: n={len(rs)} mean {st.mean(r for _, r in rs):.3f} range {min(r for _, r in rs):.3f}-{max(r for _, r in rs):.3f}  " + " ".join(f"{s}:{r:.3f}" for s, r in rs))
for k, v in sorted(c.items()):
    if not v[0].startswith('PASS'): print("  NONPASS", k, v)
print("  equiv:", sorted(set(v[2] for v in c.values())))
