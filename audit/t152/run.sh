#!/usr/bin/env bash
# T152: BOARD-QUEUE item 38 (research 1ea82d75e): the first automatic build -- ipow BDC_AUTO=1, sizes
# research/data/suite/board/ipow_v3_s2_sizes.vh (the flow's sizes_final.vh), seed 2, route sdf 81bbe268, 22.71 ns.
# Own rebuild in a clean worktree of 1ea82d75e with the item's own command (own toolchain), check sdf; own FF scan; own GLS
# with own oracle on own ipow vectors (t65/ipow_17.hex) and own latch / steer monitors at FAST_MIN, advA / advC (CARRY 1.0,
# no scatter), worst and SLOW_MAX.
set -u
A=/home/user/asyncfpga3/audit; L=/root/t152.log; K=ipow; H=auto_ipow_s2; W=/root/wt-t152
echo "T152 $(date -u)" > $L
git -C /root/wt-r91 worktree remove --force $W 2>/dev/null; git -C /root/wt-r91 worktree add -q --detach $W 1ea82d75e
mkdir -p $W/build; cp -r /root/wt-r91/build/frontend $W/build/
source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
( cd $W/cells && BDC_AUTO=1 NEXTPNR_SEED=2 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/suite/board/ipow_v3_s2_sizes.vh ./hw/build_bench.sh $K ) > /root/t152_build.log 2>&1
rc=$?; D=$W/cells/build/hw/${K}_bench_gen
echo "build rc=$rc; sdf $(md5sum $D/${K}_bench_gen.sdf | cut -c1-8) (item 38: 81bbe268)" >> $L
rm -rf /root/t65/$H; mkdir -p /root/t65/$H; cp $D/${K}_bench_gen.{bit,sdf} $D/${K}_bench_gen_routed.json /root/t65/$H/; cp $D/*.fasm /root/t65/$H/ 2>/dev/null; cp $W/cells/build/gen/${K}_kernel_bench.v /root/t65/$H/ 2>/dev/null
python3 $A/t67/scan_ff_own.py /root/t65/$H/*.fasm > /root/t90/ff_$H.txt 2>&1; echo "ff: $(tail -1 /root/t90/ff_$H.txt | sed 's/.*flops/flops/')" >> $L
sed 's/GLS_SCATTER=0.126/GLS_SCATTER=${SCAT:-0.126}/' $A/t142/gate.sh > /root/t152_gate.sh
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py; V=$A/t65/ipow_17.hex
one() { local T=$1 FLD=$2 C=${3:-0.21} RR=${4:-0.288} X=${5:-1} SC=${6:-0.126}
  HWD=$H GLS_SDF_FIELD=$FLD VECF=$V BAND_CHAIN=$C BAND_REST=$RR BAND_CELLX=$X SCAT=$SC timeout 7200 bash /root/t152_gate.sh $K $T
  python3 ../t65/oracle_ipow.py check $V /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
  echo "$T: $(grep agreement /root/t90/${H}_${T}_oracle.txt); runts $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$T.log); min steer margin $(grep STEERMON /root/t65/${H}_$T.log | grep -v VIOLATION | sed 's/.*udut.\(ucond_br[0-9]*\).*min_rise_margin_ps=\([0-9-]*\).*/\2 \1/' | sort -n | head -1); latch viol lines $(grep LATCHMON /root/t65/${H}_$T.log | grep -cE 'violations=[1-9]')" >> $L
  rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv; }
one fastmin min & one advA_ns band 0.20 0.31 1.0 0 & wait
one advC_ns band 0.20 0.20 1.0 0 & one worst band & wait
one slowmax max
echo DONE >> $L; echo DONE > /root/t152.done
