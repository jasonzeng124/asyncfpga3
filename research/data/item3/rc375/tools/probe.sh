#!/bin/bash
# probe.sh <kdir e.g. xorshift_s25/seed3> <t_start_ps> <t_len_ps>
# Re-runs the routed fast GLS of that route (same netlist_baked.v, same tb_fast.v,
# same prims/bd_env as fusion_bench, -DGLS_TRANSPORT_IC) with a windowed VCD of
# every top-level net, into rc375/<kdir>/.
set -e
S=/tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad
R=$S/rc375; K=$1; T0=$2; TL=$3
G=$S/k4/$K/gls; N=$R/regen/$K; O=$R/probe/$K; mkdir -p $O; cd $O
python3 - "$G/tb_fast.v" "$T0" "$TL" <<'PY'
import sys
t = open(sys.argv[1]).read()
old = 'initial if ($test$plusargs("vcd")) begin\n  $dumpfile("trace.vcd"); $dumpvars(0, tb); end'
assert old in t
t = t.replace(old, f'initial begin $dumpfile("win.vcd"); #{sys.argv[2]}; $dumpvars(1, tb.dut); $dumpvars(1, tb); #{sys.argv[3]}; $finish; end')
open("tb_probe.v", "w").write(t)
PY
iverilog -g2012 -gspecify -DGLS_TRANSPORT_IC -s tb -o probe.vvp $S/wt-k4/cells/gls/prims.v $S/wt-k4/cells/sim/bd_env.v $N/netlist_baked.v tb_probe.v
timeout 1500 vvp probe.vvp > sim.log 2>&1 || true
rm -f probe.vvp
tail -5 sim.log
