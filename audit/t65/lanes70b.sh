#!/usr/bin/env bash
# T70 positive-control attempt: held T4cd (select-unsafe) on bench seed 1 -- plain FAST_MIN, then FAST_MIN + M scatter draws 1, 2
cd /home/user/asyncfpga3/audit/t65
bash build_cds1.sh > build_cds1.log 2>&1
HWD=cds1 GLS_SDF_FIELD=min bash run3.sh collatz64 fastmin &
sleep 60; HWD=cds1 FMS_SEED=1 GLS_SDF_FIELD=min bash run3.sh collatz64 fms1 &
wait; HWD=cds1 FMS_SEED=2 GLS_SDF_FIELD=min bash run3.sh collatz64 fms2
echo DONE > lanes70b.done
