#!/usr/bin/env bash
# T130: own dynamic rule-M counterpart (t130/mon_zdata.py: mux data-LUT outputs changing after z_req rose, while z_ack is
# still low) at FAST_MIN, own vectors and oracle, on: item 28 (colsel3_20; research M clean: control), item 31 (colsel3a_20;
# research M clean), item 30 (c64sel3_10; research: 352/458 tokens late, <= 155 ps -- must show late tokens).
# v1 (no z_ack condition) counted state-B changes: item 31 umux0 975/1480 tokens, <= 501 ps -- not a valid measure.
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t130/mon_zdata.py ZACKS=umux0=bridge_i.udut.n14__0_ack,umux2=bridge_i.bench_o_ack
for r in colsel3_20:collatz:collatz:collatz_13.hex colsel3a_20:collatz:collatz:collatz_13.hex c64sel3_10:collatz64:collatz64:collatz64_14.hex; do
  IFS=: read H K O V <<< "$r"
  MON_KERNEL=/root/t65/$H/${K}_kernel_bench.v HWD=$H GLS_SDF_FIELD=min timeout 5400 bash gate.sh $K zd2_fastmin
  python3 ../t65/oracle_$O.py check ../t65/$V /root/t65/${H}_zd2_fastmin.log 2 > /root/t90/${H}_zd2_fastmin_oracle.txt 2>&1
done
echo DONE > /root/t130.done
