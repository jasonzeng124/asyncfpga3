#!/usr/bin/env bash
# T143: formal C 14e831cae (FOR-RESEARCH C33) "settle margins at the loop steers for item 35 ... 321-614 ps at the model's
# slow-carry corner"; its table leaves item 35's ucmpi0 -> ucond_br2 blank at the slow-carry corners. Own GLS of item 35
# (own build xdx55a_21) at formal's corner (chains 0.20, rest 0.20, CARRY4/F7/FF 1.0 = own advC), with own monitors, on
# xorshift_17 (t65) and on the long-rounds vectors (t142), and also with the within-die scatter off (GLS_SCATTER=0) on
# xorshift_17, since formal's arrivals carry no scatter. Reports the min rise margin at ucond_br2 / br5 / br8 / br6 / br7.
set -u
A=/home/user/asyncfpga3/audit; L=/root/t143.log; K=xorshift; H=xdx55a_21
echo "T143 $(date -u)" > $L
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py
one() { local T=$1 V=$2
  HWD=$H GLS_SDF_FIELD=band VECF=$V BAND_CHAIN=0.20 BAND_REST=0.20 BAND_CELLX=1.0 timeout 7200 bash ../t142/gate.sh $K $T
  python3 ../t65/oracle_xorshift.py check $V /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
  echo "$T: $(grep agreement /root/t90/${H}_${T}_oracle.txt); steer viol $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$T.log); min margins $(for b in 2 5 6 7 8; do grep STEERMON /root/t65/${H}_$T.log | grep "ucond_br$b.u\$LUT6" | tail -1 | sed 's/.*udut.\(ucond_br[0-9]\).*min_rise_margin_ps=\([0-9-]*\).*/\1=\2/'; done | tr '\n' ' ')" >> $L
  rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv; }
one advC17 $A/t65/xorshift_17.hex
until [ -f /root/t142.done ]; do sleep 60; done
one advClr $A/t142/xorshift_long.hex &
( sed 's/GLS_SCATTER=0.126/GLS_SCATTER=${SCAT:-0.126}/' $A/t142/gate.sh > /root/t143_gate_ns.sh
  HWD=$H GLS_SDF_FIELD=band VECF=$A/t65/xorshift_17.hex BAND_CHAIN=0.20 BAND_REST=0.20 BAND_CELLX=1.0 SCAT=0 timeout 7200 bash /root/t143_gate_ns.sh $K advC17ns
  echo "advC17ns (no scatter): $(python3 ../t65/oracle_xorshift.py check $A/t65/xorshift_17.hex /root/t65/${H}_advC17ns.log 2 | grep agreement); min margins $(for b in 2 5 6 7 8; do grep STEERMON /root/t65/${H}_advC17ns.log | grep "ucond_br$b.u\$LUT6" | tail -1 | sed 's/.*udut.\(ucond_br[0-9]\).*min_rise_margin_ps=\([0-9-]*\).*/\1=\2/'; done | tr '\n' ' ')" >> $L ) &
wait
echo DONE >> $L; echo DONE > /root/t143.done
