#!/usr/bin/env bash
# T91: dynamic test of research's rule-E hold on board item 18 (lever 5, sdf c6519c91) vs item 17 (lever 3, e88b0712):
# long counter carries (rounds 256/1024/2048/4095, board mask 12 bits) with the t83 monitors, worst+scatter and FAST_MIN.
cd /home/user/asyncfpga3/audit/t91
export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py VEC=/home/user/asyncfpga3/audit/t91/xs_long.hex
m() { H=$1; for c in long_worst:band long_fastmin:min; do MON_KERNEL=/root/t65/$H/xorshift_kernel_bench.v HWD=$H GLS_SDF_FIELD=${c##*:} TBATCH=4000000 bash gate_vec.sh xorshift ${c%%:*}
  python3 ../t65/oracle_xorshift.py check $VEC /root/t65/${H}_${c%%:*}.log 2 > /root/t91_${H}_${c%%:*}_oracle.txt 2>&1; done; }
m l5_1 & sleep 30; m l3_1 & wait
echo DONE > /root/t91.done
