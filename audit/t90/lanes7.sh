#!/usr/bin/env bash
# T90e: stress probe of the control-merge select gap (T65 row 3) on collatz lever 5: colnl + UCONTROL_MERGE0/1 = 1 only.
# seeds 1, 3; FAST_MIN and worst with t83 monitors; own oracle.
cd /home/user/asyncfpga3/audit/t90
SZF=/home/user/asyncfpga3/audit/t90/sizes_T3cdb_m01x1_bench.vh
SZ=$SZF bash build.sh colm 1 > /root/t90/build_colm_1.log 2>&1 &
SZ=$SZF R=/root/wt-r90b bash build.sh colm 3 > /root/t90/build_colm_3.log 2>&1 & wait
export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py
m() { H=$1; for c in mon_fastmin:min mon_worst:band; do MON_KERNEL=/root/t65/$H/collatz_kernel_bench.v HWD=$H GLS_SDF_FIELD=${c##*:} bash gate.sh collatz ${c%%:*}; done; }
m colm_1 & sleep 30; m colm_3 & sleep 30; bash run_per.sh collatz colm_1; wait
echo DONE > /root/t90/lanes7.done
