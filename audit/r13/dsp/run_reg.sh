#!/bin/bash
# auditor r13: registered DSP48E1 equivalence vs yosys cells_sim, 4 parts
R=${R:-$HOME/wt-r13/cells/gls}; D=$(dirname $0); W=$HOME/r13work/dsp; mkdir -p $W
for k in 0 1 2 3; do
  python3 -I $D/gen_reg_tb.py $R $k/4 > $W/tb_reg_$k.v 2> $D/gen_$k.log
  iverilog -o $W/reg_$k.vvp $W/tb_reg_$k.v $R/prims.v $D/../../r8/dsp/yosys_dsp48e1.v > $D/compile_$k.log 2>&1 || { echo compile fail $k; continue; }
done
