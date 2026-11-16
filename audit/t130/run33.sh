#!/usr/bin/env bash
# T130d: own z_data monitor (state A) on item 33 (xd_27) umux0 / umux1 / umux3 -- the muxes research's rule M rows name --
# at FAST_MIN and worst. z_ack aliases resolved by hand: umux0 -> uforkdec0's C-element = n12__0_ack; umux1 -> ulink_n8's
# uack chain = n12__1_ack; umux3 -> out0_ack = bench_o_ack. (T126k mapped only umux2: 0 late at both corners.)
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t130/mon_zdata.py MON_MUXES=umux0,umux1,umux3 ZACKS=umux0=bridge_i.udut.n12__0_ack,umux1=bridge_i.udut.n12__1_ack,umux3=bridge_i.bench_o_ack
for c in zd3_fastmin:min zd3_worst:band; do
  MON_KERNEL=/root/t65/xd_27/xorshift_kernel_bench.v HWD=xd_27 GLS_SDF_FIELD=${c##*:} timeout 5400 bash gate.sh xorshift ${c%%:*}
  python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/xd_27_${c%%:*}.log 2 > /root/t90/xd_27_${c%%:*}_oracle.txt 2>&1
done
echo DONE > /root/t130d.done
