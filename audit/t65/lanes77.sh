#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
bash ../t67/build_c64fm.sh 1 > ../t67/build_c64fm_1.log 2>&1
(HWD=c64fm_1 GLS_SDF_FIELD=min bash run2.sh collatz64 fastmin; HWD=c64fm_1 GLS_SDF_FIELD=max bash run2.sh collatz64 slowmax) &
bash ../t67/build_c64fm.sh 3 > ../t67/build_c64fm_3.log 2>&1
HWD=c64fm_1 bash run2.sh collatz64 worst
wait; echo DONE > lanes77.done
