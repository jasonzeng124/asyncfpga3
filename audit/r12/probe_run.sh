#!/bin/bash
# usage: probe_run.sh <bqN> [vectors...]  -- compile the r12 flop probe against the
# route's own netlist_baked.v and run it serially (one vvp at a time).
set -e
B=$1; shift; V=${@:-$(seq 0 15)}
CO=$HOME/r12work/wt-$B; W=$CO/cells/build/gls/gcd_hw; SRC=$CO/cells/gls
A=/home/user/asyncfpga3/audit/r12; O=$A/probe_$B; mkdir -p $O
python3 -I $A/gen_probe_ff.py $W/netlist_baked.v $HOME/r12work/probe_$B.v
cd $W
iverilog -gspecify -DGLS_TRANSPORT_IC -I. -o $HOME/r12work/probe_$B.vvp $SRC/tb_run.v netlist_baked.v $SRC/prims.v $HOME/r12work/probe_$B.v 2>&1 | grep -v 'procedural continuous' || true
for v in $V; do
  vvp $HOME/r12work/probe_$B.vvp +VEC=$v +TEND=150000 +QUIET=200000 > $O/v$v.log 2>&1
  echo "v$v $(grep -m1 RESULT $O/v$v.log) viol=$(grep -c VIOLATION $O/v$v.log)"
done
