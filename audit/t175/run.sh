#!/usr/bin/env bash
# T175: BOARD-QUEUE item 43 (research a8d94a7300): xorshift flow v10 s1, formal's proved plain move MLIR (memo), sizes / ENV from
# the spec research/data/suite/board/collatz_v10_s1.spec, post-route trims; sdf fd959b30, trimmed fasm 78aa6ac3, 16.35 ns.
# Own rebuild at research e4030c7787 with the patched toolchain (/root/audit-tc2), the spec's knobs passed to build_bench.sh
# as lane2.sh does (BDC_AUTO=1 BDC_AUTO_REWRITES=0 + ENV, BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0), trims applied with the
# flow's trim_lines.py (a build step), checked by own diff (INIT lines only), own bitstream, own FF scan, own GLS with own
# oracle (t65/oracle_xorshift.py) on own vectors (t144/xor19.hex, incl. the zero-trip call) at FAST_MIN, advA / advC no scatter, worst,
# SLOW_MAX, with own steer / latch monitors.
set -u
A=/home/user/asyncfpga3/audit; RC=a8d94a7300; W=/root/wt-t175; L=/root/t175.log; K=xorshift; T=${K}_bench_gen; H=v10_xor_s1
TC=/root/audit-tc2; PDB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PART=xc7z010clg400-1
echo "T174 $(date -u)" > $L
git -C /home/user/asyncfpga3 worktree remove --force $W 2>/dev/null; git -C /home/user/asyncfpga3 worktree add -q --detach $W $RC
mkdir -p $W/build; cp -r $W/cloud/fixtures/frontend $W/build/
cp $W/research/data/autorw/xorshift.mlir $W/build/frontend/$K/comp/handshake_transformed.mlir
echo "proved MLIR md5 $(md5sum < $W/research/data/autorw/xorshift.mlir | cut -c1-8)" >> $L
source $TC/openxc7/export.sh >/dev/null 2>&1
( cd $W/cells && env TC=$TC BDC_AUTO=1 BDC_AUTO_REWRITES=0 BDC_FORK_OUT_LINK=n11__0,n32__2 \
    NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$W/research/data/suite/board/xorshift_v10_s1_sizes.vh PNR_TIMEOUT=3600 \
    ./hw/build_bench.sh $K ) > /root/t175_build.log 2>&1
echo "build rc=$?" >> $L
D=$W/cells/build/hw/$T
echo "sdf $(md5sum < $D/$T.sdf | cut -c1-8) (item fd959b30); untrimmed fasm $(md5sum < $D/$T.fasm | cut -c1-8)" >> $L
mkdir -p /root/t65/$H; rm -f /root/t65/$H/*; cp $D/$T.sdf /root/t65/$H/
( cd $W && python3 research/tools/auto/trim_lines.py --partial $D/${T}_routed.json $D/$T.fasm /root/t65/$H/${T}_routed.json /root/t65/$H/$T.fasm $(cat research/data/suite/board/xorshift_v10_s1_trims.txt) ) > /root/t175_trim.log 2>&1
echo "trim rc=$?; trimmed fasm $(md5sum < /root/t65/$H/$T.fasm | cut -c1-8) (item 78aa6ac3); diff lines $(diff <(sort $D/$T.fasm) <(sort /root/t65/$H/$T.fasm) | grep -c '^[<>]'), non-INIT $(diff <(sort $D/$T.fasm) <(sort /root/t65/$H/$T.fasm) | grep '^[<>]' | grep -vc INIT)" >> $L
PYTHONPATH=$TC/openxc7-src/prjxray:$TC/openxc7/lib/python python3 $TC/openxc7-src/prjxray/utils/fasm2frames.py --db-root $PDB --part $PART /root/t65/$H/$T.fasm > /root/t175.frames 2>/root/t175_frames.log
$TC/openxc7/bin/xc7frames2bit --part_file $PDB/$PART/part.yaml --part_name $PART --frm_file /root/t175.frames --output_file /root/t65/$H/$T.bit > /root/t175_bit.log 2>&1
python3 $A/t67/scan_ff_own.py /root/t65/$H/$T.fasm > /root/t175_ff.txt 2>&1; echo "ff: $(tail -1 /root/t175_ff.txt | sed 's/.*flops/flops/')" >> $L
[ "${BUILD_ONLY:-0}" = 1 ] && { echo BUILT >> $L; exit 0; }
sed -e 's/GLS_SCATTER=0.126/GLS_SCATTER=${SCAT:-0.126}/' -e "s#^R=/root/wt-r90#R=$W#" $A/t142/gate.sh > /root/t175_gate.sh
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py; V=$A/t144/xor19.hex
one() { local TG=$1 FLD=$2 C=${3:-0.21} RR=${4:-0.288} X=${5:-1} SC=${6:-0.126}
  HWD=$H GLS_SDF_FIELD=$FLD VECF=$V BAND_CHAIN=$C BAND_REST=$RR BAND_CELLX=$X SCAT=$SC timeout 9000 bash /root/t175_gate.sh $K $TG
  python3 ../t65/oracle_xorshift.py check $V /root/t65/${H}_$TG.log 2 > /root/t90/${H}_${TG}_oracle.txt 2>&1
  echo "$TG: $(grep agreement /root/t90/${H}_${TG}_oracle.txt); runts $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$TG.log); min steer $(grep STEERMON /root/t65/${H}_$TG.log | grep -v VIOLATION | sed 's/.*udut.\(ucond_br[0-9]*\).*min_rise_margin_ps=\([0-9-]*\).*/\2 \1/' | sort -n | head -1); latch viol $(grep LATCHMON /root/t65/${H}_$TG.log | grep -cE 'violations=[1-9]')" >> $L
  rm -rf /root/t65/work_${H}_$TG/*.json /root/t65/work_${H}_$TG/*.tsv; }
one fastmin min & one advA_ns band 0.20 0.31 1.0 0 & wait
one advC_ns band 0.20 0.20 1.0 0 & one worst band & wait
one slowmax max
echo GLSDONE >> $L
