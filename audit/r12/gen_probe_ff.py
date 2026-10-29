#!/usr/bin/env python3
"""Auditor probe generator (r12).  Reads netlist_baked.v, finds every SLICE_FFX
instance with its baked TSU/THD, and writes a probe module that measures, per
flop, the min (CK rise - last D/CE change) = observed setup, and the min
(D/CE change - last CK rise) = observed hold, plus counts.  Independent of
gen.py (own regex over the baked netlist, not over the SDF).
usage: gen_probe_ff.py netlist_baked.v out.v [display_time_ps]"""
import re, sys
src, out = sys.argv[1], sys.argv[2]
tdisp = int(sys.argv[3]) if len(sys.argv) > 3 else 150900000
pat = re.compile(r'^\s*SLICE_FFX\s*#\((.*?)\)\s*(\S+)\s*\(')
ffs = []
for line in open(src):
    m = pat.match(line)
    if not m:
        continue
    params = dict(re.findall(r'\.(\w+)\(([^()]*)\)', m.group(1)))
    ffs.append((m.group(2), int(params.get('TSU', 0)), int(params.get('THD', 0))))
with open(out, 'w') as f:
    f.write('`timescale 1ps/1ps\nmodule probe_ff;\n')
    for n, _, _ in ffs:
        p = 'tb_run.dut.' + n
        f.write(f'  time {n}_ck=0, {n}_in=0, {n}_su=1000000000, {n}_hd=1000000000; integer {n}_nck=0, {n}_nin=0;\n')
        f.write(f'  always @(posedge {p}.CK) begin if ({n}_in>0 && $time-{n}_in < {n}_su) {n}_su=$time-{n}_in; {n}_ck=$time; {n}_nck={n}_nck+1; end\n')
        f.write(f'  always @({p}.D or {p}.CE) begin if ({n}_ck>0 && $time-{n}_ck < {n}_hd) {n}_hd=$time-{n}_ck; {n}_in=$time; {n}_nin={n}_nin+1; end\n')
    f.write(f'  initial begin #({tdisp});\n')
    for n, tsu, thd in ffs:
        f.write(f'    $display("SLACK {n} TSU={tsu} THD={thd} nck=%0d nin=%0d minsu=%0d minhd=%0d", {n}_nck, {n}_nin, {n}_su, {n}_hd);\n')
    f.write('  end\nendmodule\n')
print(f'{len(ffs)} SLICE_FFX probed -> {out}')
