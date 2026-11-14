#!/usr/bin/env bash
# T94: colnl_4 SLOW_MAX hang (lanes8 run 1: batch 4 never completes, PS TIMEOUT at 5 ms). Rerun + control colr_4 SLOW_MAX.
cd /home/user/asyncfpga3/audit/t90; V=$(ls ../t65/collatz_1?.hex)
for h in colnl_4 colr_4; do ( HWD=$h GLS_SDF_FIELD=max bash gate.sh collatz slowmax_r2; python3 ../t65/oracle_collatz.py check $V /root/t65/${h}_slowmax_r2.log 2 > /root/t90/${h}_slowmax_r2_oracle.txt 2>&1 ) & sleep 30; done; wait
echo DONE > /root/t90/lanes9.done
