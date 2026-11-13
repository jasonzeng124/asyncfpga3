#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
export EXTRA=BDC_MERGE_RES_LINK=ucontrol_merge0
TAGO=ipowr bash ../t67/build_ipowx.sh 1 > ../t67/build_ipowr_1.log 2>&1
(HWD=ipowr_1 GLS_SDF_FIELD=min bash run2.sh ipow fastmin; HWD=ipowr_1 bash run2.sh ipow worst; HWD=ipowr_1 GLS_SDF_FIELD=max bash run2.sh ipow slowmax) &
TAGO=c64r bash ../t67/build_c64x.sh 1 > ../t67/build_c64r_1.log 2>&1
HWD=c64r_1 GLS_SDF_FIELD=min bash run2.sh collatz64 fastmin; HWD=c64r_1 bash run2.sh collatz64 worst; HWD=c64r_1 GLS_SDF_FIELD=max bash run2.sh collatz64 slowmax
wait; echo DONE > lanes91.done
