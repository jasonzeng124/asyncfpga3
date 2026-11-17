#!/usr/bin/env bash
# T139 resume after a container restart: run the corners given as args (worst | advA | slowmax), as run.sh's one().
set -u
A=/home/user/asyncfpga3/audit; L=/root/t139.log; K=xorshift; H=xdx55a_21
(nohup bash $A/t139/hangdog.sh > /dev/null 2>&1 &)
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py
one() { local T=$1 FLD=$2
  HWD=$H GLS_SDF_FIELD=$FLD BAND_CHAIN=${3:-0.21} BAND_REST=${4:-0.288} BAND_CELLX=${5:-1} timeout 5400 bash ../t136/gate_adv.sh $K $T
  python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
  echo "$T: $(grep agreement /root/t90/${H}_${T}_oracle.txt); steer viol $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$T.log) [$(grep 'STEERMON VIOLATION' /root/t65/${H}_$T.log | sed 's/.*udut.\(ucond_br[0-9]*\).*/\1/' | sort | uniq -c | tr -s ' ' | tr '\n' ' ')]; min margins $(for b in 2 5 8; do grep STEERMON /root/t65/${H}_$T.log | grep "ucond_br$b.u\$LUT6" | tail -1 | sed 's/.*udut.\(ucond_br[0-9]\).*min_rise_margin_ps=\([0-9-]*\).*/\1=\2/'; done | tr '\n' ' '); latch viol lines $(grep LATCHMON /root/t65/${H}_$T.log | grep -cE 'violations=[1-9]')" >> $L
  rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv; }
for c in "$@"; do case $c in worst) one worst band;; advA) one advA band 0.20 0.31 1.0;; slowmax) one slowmax max;; esac; done
echo DONE >> $L; echo DONE > /root/t139.done
