#!/usr/bin/env bash
# T90 gate corners (FAST_MIN / worst+scatter / SLOW_MAX, t90/gate.sh = t65/run2.sh at wt-r90) + own oracle check.
cd /home/user/asyncfpga3/audit/t90
while pgrep -f run_per.sh >/dev/null; do sleep 30; done
lane() { K=$1; H=$2; O=../t65/oracle_$K.py; V=$(ls ../t65/${K}_1?.hex)
  for c in fastmin:min worst:band slowmax:max; do t=${c%%:*}; f=${c##*:}
    HWD=$H GLS_SDF_FIELD=$f bash gate.sh $K $t
    python3 $O check $V /root/t65/${H}_$t.log 2 > /root/t90/${H}_${t}_oracle.txt 2>&1; done; }
lane collatz64 c64nl_1 & sleep 30; lane collatz64 c64nl_3 & sleep 30; lane collatz colnl_3 & wait
echo DONE > /root/t90/lanes2.done
