#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
bash ../t67/build_colb.sh 2 > ../t67/build_colb_2.log 2>&1
(HWD=colb_2 GLS_SDF_FIELD=min bash run2.sh collatz fastmin; HWD=colb_2 bash run2.sh collatz worst) &
bash ../t67/build_colb.sh 3 > ../t67/build_colb_3.log 2>&1
HWD=colb_3 GLS_SDF_FIELD=min bash run2.sh collatz fastmin; HWD=colb_3 bash run2.sh collatz worst
wait; echo DONE > lanes78.done
