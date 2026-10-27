import csv, sys, glob
for f in sorted(glob.glob('rtfb_*.tsv')):
    rs = [r for r in csv.DictReader(open(f), delimiter='\t') if r.get('fast')]
    if not rs: continue
    s = rs[0]['seed']
    m = lambda c: min(rs, key=lambda r: int(r[c]))
    print(f"{s}: rows {len(rs)} min sdf {m('sdf')['sdf']} fast {m('fast')['fast']} ({m('fast')['node']}) slow {m('slow')['slow']} fastG {m('fastG')['fastG']} ({m('fastG')['node']}) slowG {m('slowG')['slowG']} ({m('slowG')['node']}) mix {m('mix')['mix']} ({m('mix')['node']}); "
          f"bandfail {sum(1 for r in rs if int(r['fastG'])<0 or int(r['slowG'])<0)} unbanded fail {sum(1 for r in rs if int(r['fast'])<0 or int(r['slow'])<0)} mixfail {sum(1 for r in rs if int(r['mix'])<0)} (env {sum(1 for r in rs if int(r['mix'])<0 and 'uenv' in r['node'])}) fbfallback {sum(int(r['fb_fallback']) for r in rs)}")
    for r in rs:
        if 'uenv1.u' == r['node'].split('urig.')[-1] or int(r['fastG']) < 0 or int(r['slowG']) < 0:
            print('   ', {k: r[k] for k in ('node','fb_pin','fb_sdf','fb_prjx(fmin,fmax,smin,smax)','req_pin_sdf','req_sdf','req_fmin','req_smin','fast','slow','fastG','slowG','mix')})
