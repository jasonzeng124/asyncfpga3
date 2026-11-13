#!/usr/bin/env bash
# T90 monitor runs (t83 latch/steer/mux monitors) at FAST_MIN and worst on the lever-5 routes, after lanes2.
cd /home/user/asyncfpga3/audit/t90
while [ ! -f /root/t90/lanes2.done ]; do sleep 30; done
export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py
m() { K=$1; H=$2; for c in mon_fastmin:min mon_worst:band; do MON_KERNEL=/root/t65/$H/${K}_kernel_bench.v HWD=$H GLS_SDF_FIELD=${c##*:} bash gate.sh $K ${c%%:*}; done; }
m collatz64 c64nl_1 & sleep 30; m collatz64 c64nl_3 & sleep 30; m collatz colnl_3 & wait
echo DONE > /root/t90/lanes3.done
