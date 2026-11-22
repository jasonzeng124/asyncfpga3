#!/usr/bin/env bash
# T182 GLS of one item-46 half: own bitstream/route from build.sh, research-head GLS host (ps7_bench v2 memories,
# +MEMDUMP/+MEMCHECK), own vectors and oracle (vec_oracle.py), own steer/latch monitors (t104/mon_both1.py), 5 corners.
set -u
HALF=$1; A=/home/user/asyncfpga3/audit; K=test_flatten_array; T=${K}_bench_gen; H=t182_$HALF; L=$A/t182/${HALF}_gls.log
export RWT=/root/wt-t182-$HALF; O=/root/t182_out/$HALF
mkdir -p /root/t65/$H; rm -f /root/t65/$H/*; cp $O/$T.sdf $O/$T.fasm $O/$T.bit /root/t65/$H/
cp $RWT/cells/build/hw/$T/${T}_routed.json /root/t65/$H/   # routed json = the untrimmed route's (trims are LUT INIT only)
echo "T182 GLS rest $HALF $(date -u)" >> $L
cd $A/t90 2>/dev/null || cd /root; export PS_MON_GEN=$A/t104/mon_both1.py; V=$A/t182/vec_own.hex
one() { local TG=$1 FLD=$2 C=${3:-0.21} RR=${4:-0.288} X=${5:-1} SC=${6:-0.126}
  HWD=$H GLS_SDF_FIELD=$FLD VECF=$V BAND_CHAIN=$C BAND_REST=$RR BAND_CELLX=$X SCAT=$SC TBATCH=4000000 timeout 20000 bash $A/t182/gate_mem.sh $K $TG
  python3 $A/t182/vec_oracle.py check $V /root/t65/${H}_$TG.log > /root/t65/${H}_${TG}_oracle.txt 2>&1
  cp /root/t65/${H}_${TG}_oracle.txt $A/t182/
  echo "$TG: $(grep agreement /root/t65/${H}_${TG}_oracle.txt); hang $(grep -c HANG /root/t65/${H}_$TG.log); memchk $(grep -o 'BENCHMEMCHK[^\n]*bad=[0-9]*' /root/t65/${H}_$TG.log | sed 's/.*bad=//' | sort -u | tr '\n' ' '); runts $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$TG.log); min steer $(grep STEERMON /root/t65/${H}_$TG.log | grep -v VIOLATION | sed 's/.*udut.\(ucond_br[0-9]*\).*min_rise_margin_ps=\([0-9-]*\).*/\2 \1/' | sort -n | head -1); br14 $(grep STEERMON /root/t65/${H}_$TG.log | grep 'ucond_br14\b' | sed 's/.*min_rise_margin_ps=\([0-9-]*\).*/\1/' | sort -n | head -1); latch viol $(grep LATCHMON /root/t65/${H}_$TG.log | grep -cE 'violations=[1-9]')" >> $L
  rm -rf /root/t65/work_${H}_$TG/*.json /root/t65/work_${H}_$TG/*.tsv; }

one advA_ns band 0.20 0.31 1.0 0
one advC_ns band 0.20 0.20 1.0 0; one worst band
one slowmax max
echo GLSDONE >> $L
