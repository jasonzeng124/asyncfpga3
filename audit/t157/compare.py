#!/usr/bin/env python3
"""Compare agentA's own results (gcc -O0; clang -O0 for test_bitint; unused_arg fill 0) with research's oracle output,
check that all build configs agree, scan sanitizer logs, and check the vector rules on the own answers."""
import glob, os
A = '/root/agentA'
ks = 'factorial iterative_division iterative_sqrt test_int16 test_loop_free unused_arg if_loop_1 if_loop_2 sumi3_mem fir test_bitint dot2 gather memsum'.split()
for k in ks:
    base = {'test_bitint': 'clang__O0', 'unused_arg': 'gcc__O0.fill0'}.get(k, 'gcc__O0')
    own = [l.split()[1] for l in open(f'{A}/out/{k}.{base}.res') if l.strip()]
    allres = {os.path.basename(f): [l.split()[1] for l in open(f) if l.strip()] for f in glob.glob(f'{A}/out/{k}.*.res')}
    cfgdis = [n for n, v in allres.items() if v != own]
    ub = []
    for f in glob.glob(f'{A}/out/{k}.*.err'):
        for l in open(f):
            if l.strip() and not l.startswith('@@CALL'): ub.append(l.strip()[:120])
    rh = open(f'{A}/rhout/{k}.exp').read().split()
    d = [i for i in range(max(len(own), len(rh))) if i >= len(own) or i >= len(rh) or own[i] != rh[i]]
    sv = [int(x, 16) for x in own]
    cons = [i for i in range(1, len(sv)) if sv[i] == sv[i - 1]]
    z = sv.count(0)
    print(f"{k:19s} n={len(own):3d} rh={len(rh):3d} differ={len(d)}{d if d else ''} cfgs={len(allres)} cfg_disagree={cfgdis} "
          f"sanitizer_msgs={len(ub)} consec_eq={cons} zeros={z} quarter_ok={z*4 <= len(sv)} distinct={len(set(sv))}")
    print('    own:', ' '.join(own))
