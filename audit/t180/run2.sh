#!/usr/bin/env bash
# T180: research 5efcd77855 counts digitsum s2 / digitdiv s2 / video_filter s1 as flow v10 PASS, finished locally.
# Own rebuild of the shipped route (it 7) from the farm's saved state (origin/claude/cluster
# results/suite13t_s5a_v10_2a_r1_r2/<task>/auto: sizes_$IT.vh, seed_$IT.txt, trim_$IT.txt), at research 97c98a411e (no flow-code
# diff from the farm's last head 94f40ad2), patched toolchain /root/audit-tc2, flow v10 knobs as lane2 passes them; sdf vs
# the result line; trims by the flow's trim_lines.py --partial, own INIT-only diff; own bitstream / FF scan; own GLS with
# own oracle (t180/oracle_digitsum.py) on own vectors (research's 18 operand pairs + 8 own) at 5 corners.
# usage: run.sh K TASK SDF [BUILD_ONLY=1]
set -u
A=/home/user/asyncfpga3/audit; RC=97c98a411e; K=$1; TASKN=$2; SDFX=$3; W=/root/wt-t180; L=/root/t180_$K.log; T=${K}_bench_gen; H=v10loc_${K}_s${SEEDTAG:-2}
TC=/root/audit-tc2; PDB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PART=xc7z010clg400-1
CP=results/${PART:-suite13t_s5a_v10_2a_r1_r2}/$TASKN/auto; IT=${IT:-7}
echo "T180 $K $(date -u)" > $L
[ -d $W ] || git -C /home/user/asyncfpga3 worktree add -q --detach $W $RC
rm -rf $W/build $W/cells/build/hw/$T; mkdir -p $W/build; cp -r $W/cloud/fixtures/frontend $W/build/
mkdir -p /root/t180_in/$K; for f in sizes_$IT.vh seed_$IT.txt trim_$IT.txt; do git -C /home/user/asyncfpga3 show origin/claude/cluster:$CP/$f > /root/t180_in/$K/$f; done
S=$(awk '{print $1}' /root/t180_in/$K/seed_$IT.txt); echo "seed $S; sizes md5 $(md5sum < /root/t180_in/$K/sizes_$IT.vh | cut -c1-8)" >> $L
source $TC/openxc7/export.sh >/dev/null 2>&1
( cd $W/cells && env TC=$TC BDC_AUTO=1 BDC_AUTO_REWRITES=0 NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 \
    BD_SIZES=/root/t180_in/$K/sizes_$IT.vh PNR_TIMEOUT=7200 ./hw/build_bench.sh $K ) > /root/t180_${K}_build.log 2>&1
echo "build rc=$?" >> $L
D=$W/cells/build/hw/$T
echo "sdf $(md5sum < $D/$T.sdf | cut -c1-8) (result line $SDFX); untrimmed fasm $(md5sum < $D/$T.fasm | cut -c1-8)" >> $L
mkdir -p /root/t65/$H; rm -f /root/t65/$H/*; cp $D/$T.sdf /root/t65/$H/
( cd $W && python3 research/tools/auto/trim_lines.py --partial $D/${T}_routed.json $D/$T.fasm /root/t65/$H/${T}_routed.json /root/t65/$H/$T.fasm $(cat /root/t180_in/$K/trim_$IT.txt) ) > /root/t180_${K}_trim.log 2>&1
echo "trim rc=$?; trimmed fasm $(md5sum < /root/t65/$H/$T.fasm | cut -c1-8); diff lines $(diff <(sort $D/$T.fasm) <(sort /root/t65/$H/$T.fasm) | grep -c '^[<>]'), non-INIT $(diff <(sort $D/$T.fasm) <(sort /root/t65/$H/$T.fasm) | grep '^[<>]' | grep -vc INIT)" >> $L
cp $D/$T.sdf /root/t180_${K}.sdf
[ "${BUILD_ONLY:-0}" = 1 ] && { echo BUILT >> $L; exit 0; }
PYTHONPATH=$TC/openxc7-src/prjxray:$TC/openxc7/lib/python python3 $TC/openxc7-src/prjxray/utils/fasm2frames.py --db-root $PDB --part $PART /root/t65/$H/$T.fasm > /root/t180.frames 2>/root/t180_frames.log
$TC/openxc7/bin/xc7frames2bit --part_file $PDB/$PART/part.yaml --part_name $PART --frm_file /root/t180.frames --output_file /root/t65/$H/$T.bit > /root/t180_bit.log 2>&1
python3 $A/t67/scan_ff_own.py /root/t65/$H/$T.fasm > /root/t180_ff.txt 2>&1; echo "ff: $(tail -1 /root/t180_ff.txt | sed 's/.*flops/flops/')" >> $L
sed -e 's/GLS_SCATTER=0.126/GLS_SCATTER=${SCAT:-0.126}/' -e "s#^R=/root/wt-r90#R=$W#" $A/t142/gate.sh > /root/t180_gate.sh
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py; V=$A/t180/vec_own.hex
one() { local TG=$1 FLD=$2 C=${3:-0.21} RR=${4:-0.288} X=${5:-1} SC=${6:-0.126}
  HWD=$H GLS_SDF_FIELD=$FLD VECF=$V BAND_CHAIN=$C BAND_REST=$RR BAND_CELLX=$X SCAT=$SC timeout 14000 bash /root/t180_gate.sh $K $TG
  python3 $A/t180/oracle_digitsum.py check $V /root/t65/${H}_$TG.log 2 > /root/t90/${H}_${TG}_oracle.txt 2>&1
  echo "$TG: $(grep agreement /root/t90/${H}_${TG}_oracle.txt); runts $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$TG.log); min steer $(grep STEERMON /root/t65/${H}_$TG.log | grep -v VIOLATION | sed 's/.*udut.\(ucond_br[0-9]*\).*min_rise_margin_ps=\([0-9-]*\).*/\2 \1/' | sort -n | head -1); latch viol $(grep LATCHMON /root/t65/${H}_$TG.log | grep -cE 'violations=[1-9]')" >> $L
  rm -rf /root/t65/work_${H}_$TG/*.json /root/t65/work_${H}_$TG/*.tsv; }
one fastmin min & one advA_ns band 0.20 0.31 1.0 0 & wait
one advC_ns band 0.20 0.20 1.0 0 & one worst band & wait
one slowmax max
echo GLSDONE >> $L
