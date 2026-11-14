#!/usr/bin/env bash
# T96: pre-audit fcolsz2 = colnl + research/data/collatz_sizes_T3cdb_nl2_bench.vh (merges at 2), own builds at wt-r91 = 8bcb16cb.
cd /home/user/asyncfpga3/audit/t90; V=$(ls ../t65/collatz_1?.hex)
for s in 2 3 4 5; do SZ=../research/data/collatz_sizes_T3cdb_nl2_bench.vh R=/root/wt-r91 bash build.sh colsz2 $s > /root/t90/build_colsz2_$s.log 2>&1; done
export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py
m() { H=$1; shift; for c in "$@"; do MON_KERNEL=/root/t65/$H/collatz_kernel_bench.v HWD=$H GLS_SDF_FIELD=${c##*:} bash gate.sh collatz ${c%%:*}; done; }
( for s in 2 3 4 5; do bash run_per.sh collatz colsz2_$s; done ) &
sleep 20; m colsz2_2 mon_fastmin:min mon_worst:band mon_slowmax:max &
sleep 20; ( for s in 3 4 5; do m colsz2_$s mon_fastmin:min; done ) &
wait; echo DONE > /root/t96.done
