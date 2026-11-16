#!/usr/bin/env bash
# T125: own replay of research selneg task 14 (item 28 s20, umux2: select latch ulink_n_index_11 stage[1] lat.odd ->
# umux2.uj0/uj1 A5 +3000 ps, all SDFs; copy /root/t65/cs3inj2_20 made by t125/inject.py). GLS FAST_MIN / worst with own
# oracle and the pin-level select monitor (t116/mon_sel.py) on umux2 incl. the joins' A5 pins.
cd /home/user/asyncfpga3/audit/t90
export MON_KERNEL=/root/t65/cs3inj2_20/collatz_kernel_bench.v MON_MUXES=umux2 JOIN_PINS=A5 ZACKS=umux2=bridge_i.bench_o_ack
export PS_MON_GEN=/home/user/asyncfpga3/audit/t116/mon_sel.py
for c in inj2_fastmin:min inj2_worst:band; do
  HWD=cs3inj2_20 GLS_SDF_FIELD=${c##*:} timeout 3600 bash gate.sh collatz ${c%%:*}
  python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/cs3inj2_20_${c%%:*}.log 2 > /root/t90/cs3inj2_20_${c%%:*}_oracle.txt 2>&1
done; echo DONE > /root/t125.done
