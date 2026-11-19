#!/usr/bin/env python3
"""runsim.py KERNEL VECFILE -- drive research's BDC_AUTO=1 emitted Verilog (/root/agentJ/v/<k>.v, pre-route,
sim/bd_prims_sim.v) with simcheck's testbench generator, expected values from MY gcc oracle (oracle_<k>), and
print every observed output."""
import os, sys, subprocess, re
RS = '/root/agentJ/rs'
sys.path.insert(0, os.path.join(RS, 'bdc'))
os.environ['BDC_AUTO'] = '1'
import emit, simcheck
from hs import parse
k, vf = sys.argv[1], sys.argv[2]
mlir = f'{RS}/cloud/fixtures/frontend/{k}/comp/handshake_transformed.mlir'
func = [f for f in parse.parse_module(open(mlir).read(), filename=mlir) if not f.is_declaration][0]
vecs = [list(map(int, l.split())) for l in open(vf) if l.strip()]
oracle = subprocess.run([f'./oracle_{k}'], input=''.join(' '.join(map(str, v)) + '\n' for v in vecs),
                        capture_output=True, text=True, check=True).stdout.split()
dargs = [a for a in func.args if not a.raw.startswith('memref') and not a.is_control]
res = [r for r in func.results if not r.is_control]
assert len(res) == 1 and len(dargs) == len(vecs[0]), (dargs, res)
vectors = [{a.name: x for a, x in zip(dargs, v)} for v in vecs]
expected = [{res[0].name: int(o)} for o in oracle]
tb = f'tb_{k}'
txt = simcheck.gen_testbench(func, vectors, expected, tb, f'bdc_{k}', timeout_ps=int(sys.argv[3]) if len(sys.argv) > 3 else None)
b = emit.portname(res[0].name)
txt = re.sub(r'(        if \(' + b + r'_snk\.seen\[(\d+)\] !==)',
             lambda m: f'        $display("OUT {m.group(2)} %0d", $signed({b}_snk.seen[{m.group(2)}]));\n' + m.group(1), txt)
open(f'{tb}.v', 'w').write(txt)
C = f'{RS}/cells'
cmd = (f'iverilog -g2012 -gspecify -Wno-timescale -DBD_ROUTE_PS=0 -o {tb}.vvp {C}/sim/bd_prims_sim.v {C}/sim/bd_env.v '
       f'{C}/rtl/*.v ' + os.environ.get("DUT", "/root/agentJ/v/" + k + ".v") + f' {tb}.v')
subprocess.run(cmd, shell=True, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
out = subprocess.run(['vvp', '-n', f'{tb}.vvp'], capture_output=True, text=True).stdout
got = {int(m.group(1)): int(m.group(2)) for m in re.finditer(r'OUT (\d+) (-?\d+)', out)}
mism = [(i, vecs[i], got.get(i), int(oracle[i])) for i in range(len(vecs)) if got.get(i) != int(oracle[i])]
print(f'{k}: {len(vecs)} vectors, {len(got)} outputs seen, {len(mism)} mismatches vs own gcc;',
      'PASS' if f'{tb} PASS' in out else 'tb-FAIL', mism[:5])
for l in out.splitlines():
    if 'FAIL' in l or 'timeout' in l: print('  ', l)
