#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
HWD=ipowr_1 bash run2.sh ipow worst; HWD=c64r_1 bash run2.sh collatz64 worst
HWD=ipowr_1 GLS_SDF_FIELD=max bash run2.sh ipow slowmax; HWD=c64r_1 GLS_SDF_FIELD=max bash run2.sh collatz64 slowmax
echo DONE > lanes93.done
