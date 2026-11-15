#!/usr/bin/env bash
# T117b: select-arrival lateness at the mux pins (t116/mon_sel.py) on item 28's route colsel3_20, umux0 / umux1, FAST_MIN + worst
until [ -f /root/t117.done ]; do sleep 30; done
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t116/mon_sel.py MON_KERNEL=/root/t65/colsel3_20/collatz_kernel_bench.v MON_MUXES=umux0,umux1 ZACKS=umux0=bridge_i.udut.n14__0_ack
for c in late_fastmin:min late_worst:band; do
  HWD=colsel3_20 GLS_SDF_FIELD=${c##*:} bash gate.sh collatz ${c%%:*}
  python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/colsel3_20_${c%%:*}.log 2 > /root/t90/colsel3_20_${c%%:*}_oracle.txt 2>&1
done; echo DONE > /root/t117b.done
