#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t67
for b in "l5 1" "l3 1" "l5 3" "l3 3"; do set -- $b; bash build_lev.sh $1 $2 > build_${1}_$2.log 2>&1; grep -c "ulink_n30__1 (" /root/t67/${1}_$2/xorshift_kernel_bench.v > ${1}_$2.n30count; bash run.sh ${1}_$2 & done
wait; echo DONE > lanes84.done
