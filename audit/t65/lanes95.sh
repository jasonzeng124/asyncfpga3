#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py
for s in 1 3; do bash ../t67/build_lev.sh l7 $s > ../t67/build_l7_$s.log 2>&1; ln -sfn /root/t67/l7_$s /root/t65/l7_$s; done
for s in 1 3; do MON_KERNEL=/root/t67/l7_$s/xorshift_kernel_bench.v HWD=l7_$s GLS_SDF_FIELD=min bash run2.sh xorshift mon_fastmin; done
for s in 1 3; do MON_KERNEL=/root/t67/l7_$s/xorshift_kernel_bench.v HWD=l7_$s bash run2.sh xorshift mon_worst; done
echo DONE > lanes95.done
