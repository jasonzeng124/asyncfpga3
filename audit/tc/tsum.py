import csv, sys
pre = sys.argv[1]
for s in ('d','bq2','bq3','4'):
    rs=list(csv.DictReader(open(f'{pre}_{s}.tsv'),delimiter='\t'))
    for rule in ('A','F','H','I'):
        x=[r for r in rs if r['rule']==rule]
        if not x: print(s,rule,'none'); continue
        m=lambda c: min(x,key=lambda r:int(r[c]))
        cnt=lambda c: sum(1 for r in x if int(r[c])<0)
        print(f"{s} {rule} n{len(x)} sdf_rule {m('sdf_rule')['sdf_rule']} | fast {m('fast_raw')['fast_raw']} ({m('fast_raw')['row']}) [{cnt('fast_raw')}] slow {m('slow_raw')['slow_raw']} [{cnt('slow_raw')}] | fastG {m('fastG')['fastG']} ({m('fastG')['row']}) [{cnt('fastG')}] slowG {m('slowG')['slowG']} ({m('slowG')['row']}) [{cnt('slowG')}] | mix {m('mix_raw')['mix_raw']} ({m('mix_raw')['row']}) [{cnt('mix_raw')}] | own-guard@smax {m('smax_rule')['smax_rule']} [{cnt('smax_rule')}]")
    for r in rs:
        if r['rule'] in 'AF' and any(k in r['row'] for k in ('ushli0','ushrsi','ucmpi8','merge12.udly','uaddi0','ucmpi2')) or (r['rule']=='H' and ('falseResult_55.many.stage[1]' in r['row'] or 'n143.many.stage[1]' in r['row'])):
            print('   ', r['rule'], r['row'], {k:r[k] for k in ('sdf_raw','fast_raw','slow_raw','fastG','slowG','mix_raw')})
