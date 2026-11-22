#!/usr/bin/env bash
# T186 GLS of one item-47 route: own bits (build.sh), research-head GLS host, own vectors + own oracle
# (oracle_quadrec.py, from quadrec.c, = gcc 15/15), own steer/latch monitors, 5 corners (2 at a time).
set -u
HALF=$1; A=/home/user/asyncfpga3/audit; K=quadrec; T=${K}_bench_gen; H=t186_$HALF; L=$A/t186/${HALF}_gls.log
export RWT=/root/wt-t186-$HALF; O=/root/t186_out/$HALF
mkdir -p /root/t65/$H; rm -f /root/t65/$H/*; cp $O/$T.sdf $O/$T.fasm $O/$T.bit /root/t65/$H/
cp $RWT/cells/build/hw/$T/${T}_routed.json /root/t65/$H/
echo "T186 GLS $HALF $(date -u)" >> $L
cd /root; export PS_MON_GEN=$A/t104/mon_both1.py; V=$A/t186/vec_own.hex
one() { local TG=$1 FLD=$2 C=${3:-0.21} RR=${4:-0.288} X=${5:-1} SC=${6:-0.126}
  HWD=$H GLS_SDF_FIELD=$FLD VECF=$V BAND_CHAIN=$C BAND_REST=$RR BAND_CELLX=$X SCAT=$SC TBATCH=1000000 timeout 20000 bash $A/t182/gate_mem.sh $K $TG
  python3 $A/t186/oracle_quadrec.py check $V /root/t65/${H}_$TG.log 2 > $A/t186/${H}_${TG}_oracle.txt 2>&1
  echo "$TG: $(grep agreement $A/t186/${H}_${TG}_oracle.txt); hang $(grep -c HANG /root/t65/${H}_$TG.log); sum latmax cycles $(grep -o 'latmax=[0-9]*' /root/t65/${H}_$TG.log | awk -F= '{s+=$2} END{print s}'); runts $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$TG.log); min steer $(grep STEERMON /root/t65/${H}_$TG.log | grep -v VIOLATION | sed 's/.*udut.\(ucond_br[0-9]*\).*min_rise_margin_ps=\([0-9-]*\).*/\2 \1/' | sort -n | head -1); latch viol $(grep LATCHMON /root/t65/${H}_$TG.log | grep -cE 'violations=[1-9]')" >> $L
  rm -rf /root/t65/work_${H}_$TG/*.json /root/t65/work_${H}_$TG/*.tsv; }
one fastmin min & one advA_ns band 0.20 0.31 1.0 0 & wait
one advC_ns band 0.20 0.20 1.0 0 & one worst band & wait
one slowmax max
echo GLSDONE >> $L
