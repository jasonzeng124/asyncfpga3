#!/usr/bin/env python3
"""T93 (audit, own code): run rule_e.py over designs A/B x worst/fastmin, the secondary launches, and the
planted-error tests; write results.json and results.txt here.  Reads only; never runs the project's tools or vvp."""
import subprocess, json, os, re, shutil, sys
H = os.path.dirname(os.path.abspath(__file__))
RJ = {'A': '/root/t65/l5_1/xorshift_bench_gen_routed.json', 'B': '/root/t65/l3_1/xorshift_bench_gen_routed.json'}
WD = {('A', 'worst'): '/root/t65/work_l5_1_long2_worst', ('A', 'fastmin'): '/root/t65/work_l5_1_long_fastmin',
      ('B', 'worst'): '/root/t65/work_l3_1_long2_worst', ('B', 'fastmin'): '/root/t65/work_l3_1_long_fastmin'}
# (label, design, launch link, extra args)
CHECKS = [
    ('A main: launch ulink_n7', 'A', 'ulink_n7', []),
    ('B main: launch ulink_n30__1 (latch d assumed set up)', 'B', 'ulink_n30__1', []),
    ('B combined: launch ulink_n7, ulink_n30__1 transparent', 'B', 'ulink_n7', ['--transparent', 'ulink_n30__1']),
    ('A other operand: launch ulink_n11__1', 'A', 'ulink_n11__1', []),
    ('B other operand: launch ulink_n11__1', 'B', 'ulink_n11__1', []),
]
BITS = [11, 12, 32]

def run(work, rj, link, extra, jpath):
    cmd = [sys.executable, os.path.join(H, 'rule_e.py'), work, rj, link, '--json', jpath, '--quiet'] + extra
    for b in BITS: cmd += ['--bits', str(b)]
    subprocess.run(cmd, check=True)
    return json.load(open(jpath))

out, lines = {'checks': [], 'plants': []}, []
tmpj = os.path.join(H, '_tmp.json')
for label, des, link, extra in CHECKS:
    for corner in ('worst', 'fastmin'):
        r = run(WD[(des, corner)], RJ[des], link, extra, tmpj)
        for st in r['steers']:
            row = dict(check=label, design=des, corner=corner, lut=st['name'].split('.')[-1], s_max=st['s_max'],
                       req_min=st['req_min'], margin=st['margin'],
                       diag_plain_min_margin=st['req_plain_min_diag'] - st['s_max'],
                       diag_or_join_margin=st['req_orjoin_diag'] - st['s_max'],
                       restricted={k: v['margin'] for k, v in st['restricted'].items()},
                       s_path=st['s_path'], req_path=st['req_path'],
                       restricted_paths={k: v['s_path'] for k, v in st['restricted'].items()},
                       s_cone=st['s_cone'], req_cone_cells=st['req_cone_cells'], req_notes=st['req_notes'])
            out['checks'].append(row)
            lines.append(f"{label:<56} {corner:<8} {row['lut']:<5} s_max {row['s_max']:>6}  req_min {row['req_min']:>6}"
                         f"  MARGIN {row['margin']:>6}  <2^11 {row['restricted']['11']:>6}  <2^12 {row['restricted']['12']:>6}"
                         f"  | diag OR-join {row['diag_or_join_margin']:>6}  plain-min {row['diag_plain_min_margin']:>6}")

# ---- planted-error tests (design A, worst): edit a COPY of netlist_baked.v, not the parser ----
base = [c for c in out['checks'] if c['check'].startswith('A main') and c['corner'] == 'worst']
b6 = [c for c in base if c['lut'] == 'u$LUT6'][0]
src = WD[('A', 'worst')]
pd = os.path.join(H, '_plant')
os.makedirs(pd, exist_ok=True)
for f in ('names.map', 'nets.map', 'annot.sdf'):
    if not os.path.exists(os.path.join(pd, f)): os.symlink(os.path.join(src, f), os.path.join(pd, f))
PLANTS = [('ic_012664', 'ICBUF into the LUT6 s pin (all s paths of u$LUT6 only)'),
          ('ic_019377', 'ICBUF on the full-carry critical s path, upper adder slice (not in the <2^12 cone)'),
          ('ic_016575', 'ICBUF on the critical s path in adder slice 0 (in every cone)'),
          ('ic_022049', 'ICBUF inside the ucmpi1 request delay chain (req side: margin must RISE)')]
txt = open(os.path.join(src, 'netlist_baked.v')).read()
for ic, why in PLANTS:
    m = re.search(r'ICBUF #\(\.D\((\d+)\)\) ' + ic + r' ', txt)
    d0 = int(m[1])
    mod = txt.replace(m[0], f'ICBUF #(.D({d0 + 2000})) {ic} ', 1)
    open(os.path.join(pd, 'netlist_baked.v'), 'w').write(mod)
    r = run(pd, RJ['A'], 'ulink_n7', [], tmpj)
    for st in r['steers']:
        b = [c for c in base if c['lut'] == st['name'].split('.')[-1]][0]
        row = dict(icbuf=ic, why=why, D_before=d0, D_after=d0 + 2000, lut=st['name'].split('.')[-1],
                   margin_before=b['margin'], margin_after=st['margin'], delta=st['margin'] - b['margin'],
                   r12_before=b['restricted']['12'], r12_after=st['restricted']['12']['margin'],
                   delta12=st['restricted']['12']['margin'] - b['restricted']['12'])
        out['plants'].append(row)
        lines.append(f"PLANT {ic} +2000 ps ({why}) {row['lut']}: margin {b['margin']} -> {st['margin']} "
                     f"(delta {row['delta']}), <2^12 {b['restricted']['12']} -> {row['r12_after']} (delta {row['delta12']})")
shutil.rmtree(pd); os.remove(tmpj)
json.dump(out, open(os.path.join(H, 'results.json'), 'w'), indent=1)
open(os.path.join(H, 'results.txt'), 'w').write('\n'.join(lines) + '\n')
print('\n'.join(lines))
