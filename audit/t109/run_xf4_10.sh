#!/usr/bin/env bash
# T109: GLS with t109/mon_h.py (dynamic rule H) on item 23's route at 3 corners + xf2_1 FAST_MIN (positive control:
# the route that failed). Static rows: t109/rule_h_*.txt (rule_h.py, run beforehand).
cd /home/user/asyncfpga3/audit/t90
RJ=/root/t65/xf4_10/xorshift_bench_gen_routed.json
export PS_MON_GEN=/home/user/asyncfpga3/audit/t109/mon_h.py H_JSON=/home/user/asyncfpga3/audit/t109/h_xf4_10_worst.json H_THRESH=500
for c in h_fastmin:min h_worst:band h_slowmax:max; do
  ( HWD=xf4_10 GLS_SDF_FIELD=${c##*:} bash gate.sh xorshift ${c%%:*}
    python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/xf4_10_${c%%:*}.log 2 > /root/t90/xf4_10_${c%%:*}_oracle.txt 2>&1 ) &
  sleep 30
done
( H_JSON=/home/user/asyncfpga3/audit/t109/h_xf2_1_fastmin.json HWD=xf2_1 GLS_SDF_FIELD=min bash gate.sh xorshift h_fastmin
  python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/xf2_1_h_fastmin.log 2 > /root/t90/xf2_1_h_fastmin_oracle.txt 2>&1 ) &
wait; echo DONE > /root/t109.done
