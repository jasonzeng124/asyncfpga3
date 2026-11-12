#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py MON_KERNEL=/root/t67/pmf_1/xorshift_kernel_bench.v
HWD=pmf_1 bash run2.sh xorshift mon6_worst & sleep 30; HWD=pmf_1 GLS_SDF_FIELD=min bash run2.sh xorshift mon6_fastmin; wait
echo DONE > lanes87.done
