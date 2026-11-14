#!/usr/bin/env bash
# T91 after the container restart: worst+scatter on the remaining long vectors (xs_long2), then FAST_MIN on all (xs_long).
cd /home/user/asyncfpga3/audit/t91
export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py
m() { H=$1; for c in long2_worst:band:xs_long2 long_fastmin:min:xs_long; do IFS=: read t f v <<< "$c"; export VEC=/home/user/asyncfpga3/audit/t91/$v.hex
  MON_KERNEL=/root/t65/$H/xorshift_kernel_bench.v HWD=$H GLS_SDF_FIELD=$f TBATCH=4000000 bash gate_vec.sh xorshift $t
  python3 ../t65/oracle_xorshift.py check $VEC /root/t65/${H}_$t.log 2 > /root/t65/${H}_${t}_oracle.txt 2>&1; done; }
m l5_1 & sleep 30; m l3_1 & wait
echo DONE > /root/t91b.done
