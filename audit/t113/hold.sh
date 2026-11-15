#!/usr/bin/env bash
# T113b: dynamic rule H (t109/mon_h.py, signed fix) on c64eq_25 rows < 500 ps static (worst), FAST_MIN + worst + SLOW_MAX.
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t109/mon_h.py H_JSON=/home/user/asyncfpga3/audit/t109/h_c64eq_25_worst.json H_THRESH=500
for c in h_fastmin:min h_worst:band h_slowmax:max; do
  ( HWD=c64eq_25 GLS_SDF_FIELD=${c##*:} bash gate.sh collatz64 ${c%%:*}
    python3 ../t65/oracle_collatz64.py check ../t65/collatz64_14.hex /root/t65/c64eq_25_${c%%:*}.log 2 > /root/t90/c64eq_25_${c%%:*}_oracle.txt 2>&1 ) & sleep 30
done; wait; echo DONE > /root/t113b.done
