#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t90; export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py
MON_KERNEL=/root/t65/colr_1/collatz_kernel_bench.v HWD=colr_1 GLS_SDF_FIELD=min bash gate.sh collatz mon_fastmin &
sleep 30; MON_KERNEL=/root/t65/c64r_1/collatz64_kernel_bench.v HWD=c64r_1 GLS_SDF_FIELD=min bash gate.sh collatz64 mon_fastmin; wait
echo DONE > /root/t99.done
