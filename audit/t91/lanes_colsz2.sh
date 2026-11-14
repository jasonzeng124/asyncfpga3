#!/usr/bin/env bash
# T92: colsz seeds 2-8: period (itercost corner) + FAST_MIN with t83 monitors + own oracle. Waits for T91b.
cd /home/user/asyncfpga3/audit/t90
while [ ! -f /root/t91b.done ]; do sleep 30; done
export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py
one() { for s in "$@"; do H=colsz_$s; bash run_per.sh collatz $H
  MON_KERNEL=/root/t65/$H/collatz_kernel_bench.v HWD=$H GLS_SDF_FIELD=min bash gate.sh collatz mon_fastmin; done; }
one 2 5 8 & sleep 30; one 3 6 & sleep 30; one 4 7 & wait
echo DONE > /root/t92.done
