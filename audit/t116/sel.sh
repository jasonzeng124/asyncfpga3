#!/usr/bin/env bash
# T116b: classify colsel0_24's select changes by z_req / z_ack (t116/mon_sel.py), FAST_MIN then worst.
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t116/mon_sel.py MON_KERNEL=/root/t65/colsel0_24/collatz_kernel_bench.v MON_MUXES=umux0 ZACKS=umux0=bridge_i.udut.n14__0_ack
for c in sel_fastmin:min sel_worst:band; do
  HWD=colsel0_24 GLS_SDF_FIELD=${c##*:} bash gate.sh collatz ${c%%:*}
  python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/colsel0_24_${c%%:*}.log 2 > /root/t90/colsel0_24_${c%%:*}_oracle.txt 2>&1
done; echo DONE > /root/t116b.done
