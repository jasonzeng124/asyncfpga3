#!/usr/bin/env bash
# T144: formal C36 (5a5495179's FOR-RESEARCH; shard C 11:20 UTC) "item 35 (board route 21) ... ucmpi0 -> ucond_br2 15 ps,
# 5 runts at chains 0.20 / rest 0.31 / CARRY 1.0; 17 ps at 0.20 / 0.20 / 1.0" (no scatter; vectors xor19 + xorlong), vs own
# T139 / T142 / T143 (264 / 140 ps with scatter at advA; 213 ps no scatter at advC on xorshift_17). Own build xdx55a_21,
# own monitors, own oracle, on xor19 (research's gate vectors, copied to t144/xor19.hex) at advA and advC, with and without
# the within-die scatter. Reports select changes under req (= runts) and min rise margins per steer.
set -u
A=/home/user/asyncfpga3/audit; L=/root/t144.log; K=xorshift; H=xdx55a_21; V=$A/t144/xor19.hex
echo "T144 $(date -u)" > $L
sed 's/GLS_SCATTER=0.126/GLS_SCATTER=${SCAT:-0.126}/' $A/t142/gate.sh > /root/t144_gate.sh
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py
one() { local T=$1 C=$2 R=$3 S=$4
  HWD=$H GLS_SDF_FIELD=band VECF=$V BAND_CHAIN=$C BAND_REST=$R BAND_CELLX=1.0 SCAT=$S timeout 7200 bash /root/t144_gate.sh $K $T
  python3 ../t65/oracle_xorshift.py check $V /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
  echo "$T [chains $C rest $R cells 1.0 scatter $S]: $(grep agreement /root/t90/${H}_${T}_oracle.txt); runts $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$T.log) [$(grep 'STEERMON VIOLATION' /root/t65/${H}_$T.log | sed 's/.*t=\([0-9]*\) .*udut.\(ucond_br[0-9]*\).*/\2@\1/' | sort -u | tr '\n' ' ')]; min margins $(for b in 2 5 6 7 8; do grep STEERMON /root/t65/${H}_$T.log | grep "ucond_br$b.u\$LUT6" | tail -1 | sed 's/.*udut.\(ucond_br[0-9]\).*min_rise_margin_ps=\([0-9-]*\).*/\1=\2/'; done | tr '\n' ' ')" >> $L
  rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv; }
one x19advA_ns 0.20 0.31 0 & one x19advC_ns 0.20 0.20 0 & wait
one x19advA 0.20 0.31 0.126 & one x19advC 0.20 0.20 0.126 & wait
echo DONE >> $L; echo DONE > /root/t144.done
