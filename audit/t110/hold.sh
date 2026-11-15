#!/usr/bin/env bash
# T110b: dynamic rule H (t109/mon_h.py) on xd_10's falseResult_9 stage[1] row and every row < 500 ps, FAST_MIN + worst.
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t109/mon_h.py H_JSON=/home/user/asyncfpga3/audit/t109/h_xd_10_worst.json H_THRESH=500
for c in h_fastmin:min h_worst:band; do
  ( HWD=xd_10 GLS_SDF_FIELD=${c##*:} bash gate.sh xorshift ${c%%:*}
    python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/xd_10_${c%%:*}.log 2 > /root/t90/xd_10_${c%%:*}_oracle.txt 2>&1 ) & sleep 30
done; wait; echo DONE > /root/t110b.done
