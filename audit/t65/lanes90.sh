#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py
MON_KERNEL=/root/t65/c64fm_1/collatz64_kernel_bench.v HWD=c64fm_1 GLS_SDF_FIELD=min bash run2.sh collatz64 mon_fastmin &
sleep 60; MON_KERNEL=/root/t67/l3_1/xorshift_kernel_bench.v HWD=l3_1 GLS_SDF_FIELD=min bash run2.sh xorshift mon_fastmin
wait; echo DONE > lanes90.done
