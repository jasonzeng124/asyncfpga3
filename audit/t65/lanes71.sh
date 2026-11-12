#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
bash ../t67/build_colb.sh 1 > ../t67/build_colb_1.log 2>&1
HWD=colb_1 GLS_SDF_FIELD=min bash run2.sh collatz fastmin
HWD=colb_1 GLS_SDF_FIELD=max bash run2.sh collatz slowmax &
HWD=colb_1 bash run2.sh collatz worst &
wait; echo DONE > lanes71.done
