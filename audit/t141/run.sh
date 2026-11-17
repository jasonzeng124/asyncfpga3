#!/usr/bin/env bash
# T141: research 66a0e9268 "collatz x0.55 FAILS on col17 (31-bit trajectories) ... old vectors were blind; checking item 31".
# Own check of the board candidates themselves on long trajectories: OWN vector file t141/collatz_long.hex
# (27, 97, own picks 60975 / 65307 / 73755 / 113383 with trajectory peaks of 30 / 29 / 28 / 32 bits, and research's
# 77671 / 94959 / 109881 at 31 / 30 / 30 bits), own oracle, own latch/steer monitors, on the own builds of
# item 31 (colsel3a_20) and item 28 (colsel3_20) at FAST_MIN / worst / SLOW_MAX; then the August collatz bitstream
# (board-measured) at FAST_MIN / SLOW_MAX (100 MHz). 2 runs at a time.
set -u
A=/home/user/asyncfpga3/audit; L=/root/t141.log; K=collatz; V=$A/t141/collatz_long.hex
echo "T141 $(date -u)" > $L
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py
one() { local H=$1 T=$2 FLD=$3 CK=${4:-12000}
  HWD=$H GLS_SDF_FIELD=$FLD VECF=$V FCLK=$CK timeout 7200 bash ../t141/gate_vec.sh $K $T
  python3 ../t65/oracle_collatz.py check $V /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
  echo "$H $T: $(grep agreement /root/t90/${H}_${T}_oracle.txt); wrong: $(awk '$NF!="OK" && $1 ~ /^[0-9]+$/ {print $2"->"$5}' /root/t90/${H}_${T}_oracle.txt | tr '\n' ' '); steer viol $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$T.log)" >> $L
  rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv; }
one colsel3a_20 long_worst band & one colsel3_20 long_worst band & wait
one colsel3a_20 long_fastmin min & one colsel3_20 long_fastmin min & wait
one colsel3a_20 long_slowmax max & one colsel3_20 long_slowmax max & wait
unset PS_MON_GEN
one aug_collatz long_fastmin min 10000 & one aug_collatz long_slowmax max 10000 & wait
echo DONE >> $L; echo DONE > /root/t141.done
