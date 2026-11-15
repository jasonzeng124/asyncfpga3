#!/usr/bin/env bash
# T109b: dynamic rule H (t109/mon_h.py) on item 24 (c64nl_17, 3 corners) and item 19 (ipowr_1, FAST_MIN + worst +
# SLOW_MAX), static rows from t109/rule_h.py on each route's worst work dir (H_THRESH 500 ps).
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t109/mon_h.py H_THRESH=500
run() { # route kernel corner field oracle vec
  ( H_JSON=/home/user/asyncfpga3/audit/t109/h_$1_worst.json HWD=$1 GLS_SDF_FIELD=$4 bash gate.sh $2 h_$3
    python3 ../t65/oracle_$5.py check ../t65/$6 /root/t65/$1_h_$3.log 2 > /root/t90/$1_h_$3_oracle.txt 2>&1 ) & sleep 30; }
run c64nl_17 collatz64 fastmin min collatz64 collatz64_14.hex
run c64nl_17 collatz64 worst band collatz64 collatz64_14.hex
run c64nl_17 collatz64 slowmax max collatz64 collatz64_14.hex
wait
run ipowr_1 ipow fastmin min ipow ipow_17.hex
run ipowr_1 ipow worst band ipow ipow_17.hex
run ipowr_1 ipow slowmax max ipow ipow_17.hex
wait; echo DONE > /root/t109b.done
