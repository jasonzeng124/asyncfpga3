#!/usr/bin/env bash
# T124: dynamic rule H (t109/mon_h.py) on item 28 (colsel3_20) at FAST_MIN and SLOW_MAX, to replay formal A abd04eb8c's
# ulink_n13.lat.pair[6] race (enable 607 vs data 1950 ps at fast mid).
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t109/mon_h.py H_THRESH=3000
for c in fastmin:min slowmax:max; do
  H_JSON=/home/user/asyncfpga3/audit/t117/h_${c%%:*}.json HWD=colsel3_20 GLS_SDF_FIELD=${c##*:} bash gate.sh collatz h_${c%%:*}
  python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/colsel3_20_h_${c%%:*}.log 2 > /root/t90/colsel3_20_h_${c%%:*}_oracle.txt 2>&1
done
echo DONE > /root/t124.done
