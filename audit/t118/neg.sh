#!/usr/bin/env bash
# T118: own replay of research ac048316's constructed select-arrival race on collatz (fcsel0 seed 24, sdf bb5fbbdb):
# +3000 ps on the two INTERCONNECT arcs ulink_n14__1 stage[1] latch -> umux1.uj0/uj1 A5 in every xray SDF (copy in
# /root/t65/colsel0inj_24). GLS with own oracle + t104 monitors + pin-level arrival monitor incl. the join LUTs' select pins.
# Expected (research): FAST_MIN no completion; worst passes. Question for the audit: does the own arrival monitor flag it?
cd /home/user/asyncfpga3/audit/t90
export MON_KERNEL=/root/t65/colsel0inj_24/collatz_kernel_bench.v MON_MUXES=umux1 JOIN_PINS=A5
export PS_MON_GEN=/home/user/asyncfpga3/audit/t116/mon_sel.py
for c in inj_worst:band inj_fastmin:min; do
  HWD=colsel0inj_24 GLS_SDF_FIELD=${c##*:} timeout 3600 bash gate.sh collatz ${c%%:*}
  python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/colsel0inj_24_${c%%:*}.log 2 > /root/t90/colsel0inj_24_${c%%:*}_oracle.txt 2>&1
done; echo DONE > /root/t118.done
