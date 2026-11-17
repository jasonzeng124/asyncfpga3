#!/usr/bin/env bash
# T142 own run: xorshift's loop counter on the longest carries the bench allows (rounds & 0xFFF): own vectors
# t142/xorshift_long.hex (rounds 1, 1023, 1024, 2047, 2048, 4095 x2 seeds, 4096 -> masked 0), own oracle (masks rounds),
# own latch/steer monitors, on item 35 (x0.55a s21, own build xdx55a_21) and item 33 (xd_27) at FAST_MIN / worst / advA /
# SLOW_MAX. Question: do UADDI0 / UCMPI* work on every carry the board can produce (then they are judgeable by vectors).
set -u
A=/home/user/asyncfpga3/audit; L=/root/t142.log; K=xorshift; V=$A/t142/xorshift_long.hex
echo "T142 $(date -u)" > $L
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py
one() { local H=$1 T=$2 FLD=$3
  HWD=$H GLS_SDF_FIELD=$FLD VECF=$V BAND_CHAIN=${4:-0.21} BAND_REST=${5:-0.288} BAND_CELLX=${6:-1} timeout 7200 bash ../t142/gate.sh $K $T
  python3 ../t65/oracle_xorshift.py check $V /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
  echo "$H $T: $(grep agreement /root/t90/${H}_${T}_oracle.txt); steer viol $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$T.log); min margins $(for b in 2 5 8; do grep STEERMON /root/t65/${H}_$T.log | grep "ucond_br$b.u\$LUT6" | tail -1 | sed 's/.*udut.\(ucond_br[0-9]\).*min_rise_margin_ps=\([0-9-]*\).*/\1=\2/'; done | tr '\n' ' '); latch viol lines $(grep LATCHMON /root/t65/${H}_$T.log | grep -cE 'violations=[1-9]')" >> $L
  rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv; }
one xdx55a_21 lr_fastmin min & one xd_27 lr_fastmin min & wait
one xdx55a_21 lr_worst band & one xdx55a_21 lr_advA band 0.20 0.31 1.0 & wait
one xdx55a_21 lr_slowmax max & one xd_27 lr_worst band & wait
echo DONE >> $L; echo DONE > /root/t142.done
