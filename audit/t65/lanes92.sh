#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
(HWD=ipowr_1 GLS_SDF_FIELD=min bash run2.sh ipow fastmin; HWD=ipowr_1 bash run2.sh ipow worst; HWD=ipowr_1 GLS_SDF_FIELD=max bash run2.sh ipow slowmax) &
sleep 60; HWD=c64r_1 GLS_SDF_FIELD=min bash run2.sh collatz64 fastmin; HWD=c64r_1 bash run2.sh collatz64 worst; HWD=c64r_1 GLS_SDF_FIELD=max bash run2.sh collatz64 slowmax
wait; echo DONE > lanes92.done
