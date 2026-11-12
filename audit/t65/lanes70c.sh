#!/usr/bin/env bash
# T70 positive-control attempt: held T4cd (select-unsafe) on bench seed 1 -- plain FAST_MIN, then FAST_MIN + M scatter draws 1, 2
# (the plain run creates the shared xray SDF first; the scatter runs start once it is complete)
cd /home/user/asyncfpga3/audit/t65
until grep -q BUILDDONE build_cds1.log 2>/dev/null; do sleep 20; done
HWD=cds1 GLS_SDF_FIELD=min bash run3.sh collatz64 fastmin &
until grep -q "md5sum\|^[0-9a-f]\{32\}  /root/t65/cds1/collatz64_bench_gen_xray_min.sdf" /root/t65/cds1_fastmin.log 2>/dev/null; do sleep 10; done
HWD=cds1 FMS_SEED=1 GLS_SDF_FIELD=min bash run3.sh collatz64 fms1 &
wait; HWD=cds1 FMS_SEED=2 GLS_SDF_FIELD=min bash run3.sh collatz64 fms2
echo DONE > lanes70b.done
