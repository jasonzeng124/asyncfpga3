#!/usr/bin/env bash
# T154: BOARD-QUEUE items 40 (automatic collatz64, flow v3, seed 5, sdf 9585dde4) and 41 (automatic xorshift, flow v3,
# seed 8, sdf 3497ca67), research 79fec0d88. As T151 / T152 / T153: own rebuild at 312abcc32 (the farm's flow-v3 commit,
# same nextpnr 9c732bc6 as the audit toolchain) with each item's own sizes file (copied here from research 7197d85c2),
# BDC_AUTO=1 and the item's command; own FF scan; own GLS with own oracle and own steer/latch monitors at FAST_MIN,
# advA / advC (CARRY 1.0, no scatter), worst (+scatter) and SLOW_MAX.
# usage: run.sh 40|41
set -u
A=/home/user/asyncfpga3/audit; I=$1
case $I in
 40) K=collatz64; S=5; SZ=$A/t154/collatz64_v3_s5_sizes.vh; H=auto_c64_s5; EXP=9585dde4; V=$A/t65/collatz64_14.hex; OR=oracle_collatz64.py;;
 41) K=xorshift; S=8; SZ=$A/t154/xorshift_v3_s8_sizes.vh; H=auto_xor_s8; EXP=3497ca67; V=$A/t144/xor19.hex; OR=oracle_xorshift.py;;
esac
L=/root/t154_$I.log; W=/root/wt-t154_$I
echo "T154 item $I $(date -u)" > $L
git -C /root/wt-r91 worktree remove --force $W 2>/dev/null; git -C /root/wt-r91 worktree add -q --detach $W 312abcc32
mkdir -p $W/build; cp -r $W/cloud/fixtures/frontend $W/build/
source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
( cd $W/cells && BDC_AUTO=1 NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh $K ) > /root/t154_${I}_build.log 2>&1
echo "build rc=$?" >> $L
D=$W/cells/build/hw/${K}_bench_gen
echo "sdf $(md5sum $D/${K}_bench_gen.sdf | cut -c1-8) (item $I $EXP)" >> $L
rm -rf /root/t65/$H; mkdir -p /root/t65/$H; cp $D/${K}_bench_gen.{bit,sdf} $D/${K}_bench_gen_routed.json /root/t65/$H/; cp $D/*.fasm /root/t65/$H/ 2>/dev/null
python3 $A/t67/scan_ff_own.py /root/t65/$H/*.fasm > /root/t90/ff_$H.txt 2>&1; echo "ff: $(tail -1 /root/t90/ff_$H.txt | sed 's/.*flops/flops/')" >> $L
[ "${BUILD_ONLY:-0}" = 1 ] && exit 0
sed 's/GLS_SCATTER=0.126/GLS_SCATTER=${SCAT:-0.126}/' $A/t142/gate.sh > /root/t154_gate.sh
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py
one() { local T=$1 FLD=$2 C=${3:-0.21} RR=${4:-0.288} X=${5:-1} SC=${6:-0.126}
  HWD=$H GLS_SDF_FIELD=$FLD VECF=$V BAND_CHAIN=$C BAND_REST=$RR BAND_CELLX=$X SCAT=$SC timeout 9000 bash /root/t154_gate.sh $K $T
  python3 ../t65/$OR check $V /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
  echo "$T: $(grep agreement /root/t90/${H}_${T}_oracle.txt); runts $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$T.log); min steer margin $(grep STEERMON /root/t65/${H}_$T.log | grep -v VIOLATION | sed 's/.*udut.\(ucond_br[0-9]*\).*min_rise_margin_ps=\([0-9-]*\).*/\2 \1/' | sort -n | head -1); latch viol lines $(grep LATCHMON /root/t65/${H}_$T.log | grep -cE 'violations=[1-9]')" >> $L
  rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv; }
one fastmin min & one advA_ns band 0.20 0.31 1.0 0 & wait
one advC_ns band 0.20 0.20 1.0 0 & one worst band & wait
one slowmax max
echo DONE >> $L; echo DONE > /root/t154_$I.done
