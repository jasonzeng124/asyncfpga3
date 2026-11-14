#!/usr/bin/env bash
# T98: BOARD-QUEUE item 22 (#23, research 514ac04a): fcolsz2 seed 26 (recipe sdf bc2fe0c8) + item 20 baseline colr seed 26.
cd /home/user/asyncfpga3/audit/t90
SZ=../research/data/collatz_sizes_T3cdb_nl2_bench.vh R=/root/wt-r91 bash build.sh colsz2 26 > /root/t90/build_colsz2_26.log 2>&1
R=/root/wt-r90b bash build.sh colr 26 > /root/t90/build_colr_26.log 2>&1
python3 ../t67/scan_ff_own.py /root/t65/colsz2_26/*.fasm > /root/t90/ff_colsz2_26.txt 2>&1
export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py MON_KERNEL=/root/t65/colsz2_26/collatz_kernel_bench.v
( bash run_per.sh collatz colsz2_26; bash run_per.sh collatz colr_26 ) &
sleep 20; ( HWD=colsz2_26 GLS_SDF_FIELD=min bash gate.sh collatz mon_fastmin; HWD=colsz2_26 GLS_SDF_FIELD=max bash gate.sh collatz mon_slowmax ) &
sleep 20; HWD=colsz2_26 GLS_SDF_FIELD=band bash gate.sh collatz mon_worst; wait
echo DONE > /root/t98.done
