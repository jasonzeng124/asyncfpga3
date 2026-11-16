#!/usr/bin/env bash
# T134: coverage gap found by research 27e9752dc -- the collatz / collatz64 gate vectors (own collatz_13 / collatz64_14 too)
# contain no n = 1, so the loop-entry steers are never judged. Own vectors with n = 1 added as the 2nd vector
# (t65/collatz_14n1.hex, t65/collatz64_15n1.hex); FAST_MIN GLS with own oracle + t104 monitors on board items 28, 31 (collatz)
# and 30, 32 (collatz64).
cd /home/user/asyncfpga3/audit/t90
for r in colsel3_20:collatz:collatz_14n1.hex colsel3a_20:collatz:collatz_14n1.hex c64sel3_10:collatz64:collatz64_15n1.hex c64sel3p_22:collatz64:collatz64_15n1.hex; do
  IFS=: read H K V <<< "$r"
  export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/$H/${K}_kernel_bench.v
  VEC=/home/user/asyncfpga3/audit/t65/$V HWD=$H GLS_SDF_FIELD=min timeout 3600 bash ../t91/gate_vec.sh $K n1_fastmin
  python3 ../t65/oracle_$K.py check ../t65/$V /root/t65/${H}_n1_fastmin.log 2 > /root/t90/${H}_n1_oracle.txt 2>&1
  echo "$H: $(tail -1 /root/t90/${H}_n1_oracle.txt); vec1(n=1): $(sed -n 3p /root/t90/${H}_n1_oracle.txt | awk '{print $NF}'); nonzero LATCH/STEER violations $(grep -E 'LATCHMON|STEERMON' /root/t65/${H}_n1_fastmin.log | grep -cE 'violations=[1-9]')" >> /root/t134.log
done
echo DONE > /root/t134.done
