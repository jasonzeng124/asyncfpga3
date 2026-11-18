#!/usr/bin/env bash
# T153: BOARD-QUEUE item 39 (research 8494308c5): automatic collatz, flow v3, seed 6, sdf c56def07, 18.99 ns. Own rebuild of the
# route at 312abcc32 (same nextpnr as the audit toolchain) with the item.s own
# sizes file (copied here), with BDC_AUTO=1 and the board flags as research/tools/fifteen/lane2.sh, in a clean worktree
# of 312abcc32 (own toolchain /root/audit-tc). Then own GLS with own oracle on own long-trajectory vectors
# (t141/collatz_long.hex, incl. n = 60975, the bench's maximum peak) and own steer monitors at FAST_MIN, worst, advA / advC
# (CARRY 1.0, no scatter) and SLOW_MAX.
set -u
A=/home/user/asyncfpga3/audit; L=/root/t153.log; K=collatz; H=auto_col_s6; W=/root/wt-t153
echo "T153 $(date -u)" > $L
git -C /root/wt-r91 worktree remove --force $W 2>/dev/null; git -C /root/wt-r91 worktree add -q --detach $W 312abcc32
mkdir -p $W/build; cp -r /root/wt-r91/build/frontend $W/build/
source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
( cd $W/cells && BDC_AUTO=1 NEXTPNR_SEED=6 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$A/t153/collatz_v3_s6_sizes.vh ./hw/build_bench.sh $K ) > /root/t153_build.log 2>&1
D=$W/cells/build/hw/${K}_bench_gen
echo "build rc=$?; sdf $(md5sum $D/${K}_bench_gen.sdf | cut -c1-8) (item 39 c56def07); nextpnr $(grep -m1 -o 'nextpnr[^ ]* [0-9a-f]*' $W/cells/build/hw/toolchain.txt 2>/dev/null)" >> $L
rm -rf /root/t65/$H; mkdir -p /root/t65/$H; cp $D/${K}_bench_gen.{bit,sdf} $D/${K}_bench_gen_routed.json /root/t65/$H/; cp $D/*.fasm /root/t65/$H/ 2>/dev/null; cp $W/cells/build/gen/${K}_kernel_bench.v /root/t65/$H/ 2>/dev/null
python3 $A/t67/scan_ff_own.py /root/t65/$H/*.fasm > /root/t90/ff_$H.txt 2>&1; echo "ff: $(tail -1 /root/t90/ff_$H.txt | sed 's/.*flops/flops/')" >> $L
sed 's/GLS_SCATTER=0.126/GLS_SCATTER=${SCAT:-0.126}/' $A/t142/gate.sh > /root/t153_gate.sh
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py; V=$A/t141/collatz_long.hex
one() { local T=$1 FLD=$2 C=${3:-0.21} RR=${4:-0.288} X=${5:-1} SC=${6:-0.126}
  HWD=$H GLS_SDF_FIELD=$FLD VECF=$V BAND_CHAIN=$C BAND_REST=$RR BAND_CELLX=$X SCAT=$SC timeout 7200 bash /root/t153_gate.sh $K $T
  python3 ../t65/oracle_collatz.py check $V /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
  echo "$T: $(grep agreement /root/t90/${H}_${T}_oracle.txt); runts $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$T.log); min steer margin $(grep STEERMON /root/t65/${H}_$T.log | grep -v VIOLATION | sed 's/.*udut.\(ucond_br[0-9]*\).*min_rise_margin_ps=\([0-9-]*\).*/\2 \1/' | sort -n | head -1); latch viol lines $(grep LATCHMON /root/t65/${H}_$T.log | grep -cE 'violations=[1-9]')" >> $L
  rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv; }
one fastmin min & one advA_ns band 0.20 0.31 1.0 0 & wait
one advC_ns band 0.20 0.20 1.0 0 & one worst band & wait
one slowmax max
echo DONE >> $L; echo DONE > /root/t153.done
