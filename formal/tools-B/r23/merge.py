import json, collections
K = {}
for l in open('/home/user/asyncfpga3/formal/tools-B/ps/out/latchhold_kappa_670.txt'):
    k, n, f = l.split(); K[n] = (float(k), f)
for c in '01':
    A = {(r['latch'], r['kind'], r['c1']['B'], r['c2']['A']): r for r in json.load(open('trunc_c%s.json' % c))['rows']}
    F = {(r['latch'], r['kind'], r['Dend'], r['close']): r for r in json.load(open('trunc4_c%s.json' % c))}
    out = open('table_c%s.tsv' % c, 'w')
    out.write("latch\tkind\tenable\tD_src\troot_or_inherited\tclass\tsep_margin\tup_margin\trun_margin\tc1.B(D-claim end)\tc2.A\tguards_on_chain\tD_next_change_gap_ps\tB670_kappa\n")
    rows = []
    for k, r in A.items():
        f = F.get(k, {})
        cls = f.get('why', '')
        if 'unordered' in cls: cl = 'unordered (no common-ancestor bound; Up blocked by non-common branch)'
        elif 'Up(c1.B->c2.A) = ' in cls: cl = 'same-event anchor, finite shortfall (re-open setup)'
        elif 'missing' in cls: cl = 'D-claim anchored BEFORE c2.A; needs Up(c1.B->c2.A), blocked by non-common branch'
        else: cl = cls[:60]
        ri = 'inherited<-%s' % f['inherited_from'][0][0] if f.get('inherited_from') else 'ROOT'
        gaps = [d['gap'] for d in r['Dp'] if d['gap'] is not None]
        rows.append((r['guards_n'], k[0], k[1], r['en'], ",".join(d['src'] for d in r['Dp']), ri, cl, f.get('sep_margin'), f.get('up_via_e0') if f.get('up_direct') is None else f.get('up_direct'),
                     f.get('run_margin'), k[2], k[3], r['guards_n'], ",".join(map(str, gaps)) or "none", "%.4f" % K[k[0]][0] if k[0] in K else "-"))
    rows.sort(key=lambda x: (-x[0], x[2], x[1]))
    for x in rows: out.write("\t".join(map(str, x[1:])) + "\n")
    out.close()
    roots = [x for x in rows if x[5] == 'ROOT']
    print(c, 'rows', len(rows), 'roots', len(roots), collections.Counter((x[2], x[6]) for x in roots).most_common())
    print('  roots with guards:', [(x[1], x[2], x[0]) for x in roots if x[0]])
    print('  root latches in B670:', sum(1 for x in roots if x[14] != '-'), 'of', len(set(x[1] for x in roots)))
    ul = set(x[1] for x in roots if x[2] == 'U->H'); print('  root U->H latches', len(ul), 'in B670', sum(1 for x in ul if x in K))
