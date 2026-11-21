#!/usr/bin/env python3
"""memtb.py MLIR DUT.v VEC.hex EXP.txt OUT_TB.v -- a pre-route RTL testbench for a bdc kernel WITH memories.

DUT.v: `BDC_HOST_MEM=1 python3 bdc/emit.py MLIR --no-top -o DUT.v` (research branch).  VEC.hex: a v2 bench vector
file (research/data/suite/bench/README.md: per call the operand words, then every element of each memref in signature
order).  EXP.txt: one 8-hex-digit expected out0 per call (research/tools/suite/oracle_mem.sh).
The bench, modelled on research/tools/suite/tb_store1.v: per call, write every array through its host port, then
send one token on every argument channel (data words as the bench maps them: one word per i32, i64 low then high)
and wait for one token on every result channel; compare out0 (masked to its width).  Prints MEMTB call=J ... ok|BAD
and MEMTB SUMMARY pass|FAIL.  Zero-wire-delay arc-timing RTL (cells/sim/bd_prims_sim.v), nothing about routed timing.
"""
import re
import sys

mlir, dut, vecf, expf, outf = sys.argv[1:6]
text = open(mlir).read()
fl = [l for l in text.splitlines() if 'handshake.func' in l][0]
sig = fl[fl.index('(') + 1:fl.index(') ->')]
args = re.findall(r'%arg\d+:\s*((?:memref<[^>]*>)|(?:!handshake\.\w+<[^>]*>))', sig)
names = re.findall(r'"([^"]+)"', re.search(r'argNames = \[([^\]]*)\]', fl).group(1))
resn = re.findall(r'"([^"]+)"', re.search(r'resNames = \[([^\]]*)\]', fl).group(1))
v = open(dut).read()
mod = 'bdc_' + re.search(r'@(\w+)', fl).group(1)
hdr = v[re.search(r'module ' + mod + r'\s*#', v).start():]
hdr = hdr[:hdr.index(');') + 2]
ports = re.findall(r'(input|output)\s+wire\s+(?:\[(\d+):0\])?\s*(\w+)', hdr)
pw = {p: int(w) + 1 if w else 1 for _, w, p in ports}

vt = open(vecf).read()
words = [int(w, 16) for w in re.sub(r'//[^\n]*', ' ', vt).split()]
exp = [int(x, 16) for x in open(expf).read().split()]
data, mems = [], []
for (ty, nm) in zip(args, names):
    if ty.startswith('memref'):
        n = int(re.match(r'memref<(\d+)x', ty).group(1))
        mems.append((nm, n))
    elif 'channel' in ty:
        data.append((nm, int(re.search(r'<i(\d+)>', ty).group(1))))
calls = []
pos = 0
while pos < len(words):
    dv = {}
    for nm, w in data:
        if w == 64:
            dv[nm] = words[pos] | (words[pos + 1] << 32)
            pos += 2
        else:
            dv[nm] = words[pos] & ((1 << w) - 1)
            pos += 1
    mv = {}
    for nm, n in mems:
        mv[nm] = words[pos:pos + n]
        pos += n
    calls.append((dv, mv))
assert len(calls) == len(exp), (len(calls), len(exp))

L = ['`timescale 1ps/1ps', 'module memtb;', '    reg rst = 1;', '    integer fails = 0;', '    reg [63:0] got;']
conn = ['.rst(rst)']
for d, w, p in ports:
    if p == 'rst':
        continue
    rng = f'[{pw[p] - 1}:0] ' if pw[p] > 1 else ''
    if d == 'input':
        L.append(f'    reg {rng}{p} = 0;')
    else:
        L.append(f'    wire {rng}{p};')
    conn.append(f'.{p}({p})')
L.append(f'    {mod} dut ({", ".join(conn)});')
for nm, n in mems:
    L += [f'    task host_{nm}(input [31:0] a, input [31:0] d);',
          '        begin',
          f'            wait ({nm}_host_ack === 1\'b0);',
          f'            {nm}_host_addr = a; {nm}_host_wdata = d; {nm}_host_we = 1;',
          f'            #1000 {nm}_host_req = 1;',
          f'            wait ({nm}_host_ack === 1\'b1);',
          f'            #3000 {nm}_host_req = 0;',
          f'            wait ({nm}_host_ack === 1\'b0);',
          '            #1000;',
          '        end', '    endtask']
ins = [p[:-4] for d, w, p in ports if d == 'input' and p.endswith('_req') and not p.endswith('_host_req')]
outs = [p[:-4] for d, w, p in ports if d == 'output' and p.endswith('_req')]
L += ['    initial begin', '        #20000 rst = 0; #20000;']
for c, (dv, mv) in enumerate(calls):
    for nm, n in mems:
        for i, x in enumerate(mv[nm]):
            L.append(f"        host_{nm}({i}, 32'h{x:08x});")
    L.append('        fork')
    for ch in ins:
        setd = f"{ch}_data = {pw[ch + '_data']}'h{dv[ch]:x}; " if ch + '_data' in pw else ''
        L.append(f"            begin {setd}#200 {ch}_req = 1; wait ({ch}_ack === 1'b1); {ch}_req = 0; "
                 f"wait ({ch}_ack === 1'b0); end")
    for ch in outs:
        cap = f'got = {ch}_data; ' if ch == resn[0] and ch + '_data' in pw else ''
        L.append(f"            begin wait ({ch}_req === 1'b1); {cap}#300 {ch}_ack = 1; wait ({ch}_req === 1'b0); "
                 f"#300 {ch}_ack = 0; end")
    L.append('        join')
    w = pw.get(resn[0] + '_data', 32)
    e = exp[c] & ((1 << w) - 1)
    L.append(f"        if (got[{w - 1}:0] !== {w}'h{e:x}) fails = fails + 1;")
    L.append(f'        $display("MEMTB call={c} out0=%h exp={e:08x} %s", got[{w - 1}:0], '
             f"got[{w - 1}:0] === {w}'h{e:x} ? \"ok\" : \"BAD\");")
    L.append('        #2000;')
L += [f'        $display("MEMTB SUMMARY %s (%0d failure(s) of {len(calls)} calls) at %0t ps", fails ? "FAIL" : "pass", fails, $time);',
      '        $finish;', '    end',
      '    initial begin #2000000000; $display("MEMTB SUMMARY FAIL (timeout at %0t ps)", $time); $finish; end',
      'endmodule']
open(outf, 'w').write('\n'.join(L) + '\n')
