#!/usr/bin/env bash
# T136 resume after the 23:3x container restart: re-run the interrupted own draws (args: draw numbers), as run.sh's one().
set -u
A=/home/user/asyncfpga3/audit; L=/root/t136.log; H=xd40_27; K=xorshift
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py
one() { local T=$1 FLD=$2
  HWD=$H GLS_SDF_FIELD=$FLD BAND_CHAIN=${3:-0.21} BAND_REST=${4:-0.288} BAND_CELLX=${5:-1} SCSEED=${6:-1} timeout 5400 bash ../t136/gate_adv.sh $K $T
  python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
  echo "gate $T [$FLD ${3:-} ${4:-} ${5:-} ${6:-}]: $(grep agreement /root/t90/${H}_${T}_oracle.txt); steer violations $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$T.log)" >> $L
  rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv; }
for i in "$@"; do read c rr x <<< "$(awk -v i=$i '$1==i{print $2, $3, $4}' /root/t136_draws.txt)"; one dr$i band $c $rr $x $((136000+i)) & done; wait
echo DONE >> $L; echo DONE > /root/t136.done
