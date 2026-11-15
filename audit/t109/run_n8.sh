#!/usr/bin/env bash
# T109c: xf4_10 ulink_n8 (research tsehold candidate, ac5c4844): at the SECOND state node of the static path
# (ulink_n_trueResult_8 stage[1] controller), which input fired it last; FAST_MIN and worst.
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t109/mon_h.py H_JSON=/home/user/asyncfpga3/audit/t109/h_xf4_10_n8_second.json H_THRESH=500
for c in n8_fastmin:min n8_worst:band; do
  ( HWD=xf4_10 GLS_SDF_FIELD=${c##*:} bash gate.sh xorshift ${c%%:*}
    python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/xf4_10_${c%%:*}.log 2 > /root/t90/xf4_10_${c%%:*}_oracle.txt 2>&1 )
done; wait; echo DONE > /root/t109c.done
