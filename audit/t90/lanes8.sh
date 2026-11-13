#!/usr/bin/env bash
# T90f: worst+scatter and SLOW_MAX + own oracle on the lever-5 routes not yet gated (c64nl 2,4-9; colnl 1,2,4-8; c64nl_9 FAST_MIN too).
cd /home/user/asyncfpga3/audit/t90
g() { for h in "$@"; do case $h in c64*) K=collatz64;; *) K=collatz;; esac; V=$(ls ../t65/${K}_1?.hex)
  for c in "${CORNERS[@]}"; do t=${c%%:*}; f=${c##*:}
    HWD=$h GLS_SDF_FIELD=$f bash gate.sh $K $t; python3 ../t65/oracle_$K.py check $V /root/t65/${h}_$t.log 2 > /root/t90/${h}_${t}_oracle.txt 2>&1; done; done; }
CORNERS=(worst:band slowmax:max)
( CORNERS=(fastmin:min worst:band slowmax:max); g c64nl_9; CORNERS=(worst:band slowmax:max); g c64nl_6 colnl_4 colnl_7 ) & sleep 30
g c64nl_2 c64nl_7 colnl_1 colnl_5 & sleep 30
g c64nl_4 c64nl_5 c64nl_8 colnl_2 colnl_6 colnl_8 & wait
echo DONE > /root/t90/lanes8.done
