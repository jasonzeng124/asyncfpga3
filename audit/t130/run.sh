#!/usr/bin/env bash
# T130: own dynamic rule-M counterpart (t130/mon_zdata.py: mux data-LUT outputs changing after z_req rose) on item 31
# (colsel3a_20; research: M clean, data leads z_req >= 1.6 ns) and item 30 (c64sel3_10; research: 352/458 tokens late, up
# to 155 ps at FAST_MIN), FAST_MIN, own vectors and oracle. Negative/positive control pair: item 30 must show late tokens.
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t130/mon_zdata.py
for r in colsel3a_20:collatz:collatz:collatz_13.hex c64sel3_10:collatz64:collatz64:collatz64_14.hex; do
  IFS=: read H K O V <<< "$r"
  MON_KERNEL=/root/t65/$H/${K}_kernel_bench.v HWD=$H GLS_SDF_FIELD=min timeout 5400 bash gate.sh $K zd_fastmin
  python3 ../t65/oracle_$O.py check ../t65/$V /root/t65/${H}_zd_fastmin.log 2 > /root/t90/${H}_zd_fastmin_oracle.txt 2>&1
done
echo DONE > /root/t130.done
