#!/usr/bin/env bash
# T90d: FAST_MIN + own oracle on every remaining lever-5 route (c64nl 2,4-8; colnl 1,2,4-8).
cd /home/user/asyncfpga3/audit/t90
f() { for h in "$@"; do case $h in c64*) K=collatz64;; *) K=collatz;; esac; V=$(ls ../t65/${K}_1?.hex)
  HWD=$h GLS_SDF_FIELD=min bash gate.sh $K fastmin; python3 ../t65/oracle_$K.py check $V /root/t65/${h}_fastmin.log 2 > /root/t90/${h}_fastmin_oracle.txt 2>&1; done; }
f c64nl_2 c64nl_6 colnl_1 colnl_5 colnl_8 & sleep 30; f c64nl_4 c64nl_7 colnl_2 colnl_6 & sleep 30; f c64nl_5 c64nl_8 colnl_4 colnl_7 & wait
echo DONE > /root/t90/lanes6.done
