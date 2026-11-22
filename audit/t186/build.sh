#!/usr/bin/env bash
# T186: BOARD-QUEUE item 47 (research e454144a54, quadrec s3 v10 vs v13local). Copy of t182/build.sh with MLIR override.
# Own rebuild of each half from its spec, at research head (no use of board_rebuild.sh): build_bench.sh with the
# board flags + spec ENV, sdf md5 vs spec; trims via the flow's trim_lines.py --partial (tool under test) with spec ENV,
# then own checks: refusals, INIT-only diff, trimmed fasm md5 vs spec; own bitstream (fasm2frames + xc7frames2bit).
# usage: build.sh HALF(unpadded|padded) RC
set -u
HALF=$1; RC=$2; A=/home/user/asyncfpga3/audit; W=/root/wt-t186-$HALF; L=$A/t186/$HALF.log
TC=/root/audit-tc2; PDB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PART=xc7z010clg400-1
SP=research/data/keepdepth/board/$HALF/quadrec.spec
[ -d $W ] || git -C /home/user/asyncfpga3 worktree add -q --detach $W $RC
get() { sed -n "s/^$1=//p" $W/$SP | head -1; }
M=$(get MLIR); K=$(get K); S=$(get SEED); Z=$(get SIZES); TR=$(get TRIMS); XE=$(get ENV); WS=$(get SDF); WF=$(get FASM); T=${K}_bench_gen
echo "T182 $HALF at $RC $(date -u); K=$K S=$S sizes=$(md5sum < $W/$Z | cut -c1-8) ENV=[$XE] want sdf $WS fasm $WF" > $L
rm -rf $W/build $W/cells/build/hw/$T; mkdir -p $W/build; cp -r $W/cloud/fixtures/frontend $W/build/; [ "$M" != - ] && cp $W/$M $W/build/frontend/$K/comp/handshake_transformed.mlir && echo "mlir $(md5sum < $W/$M | cut -c1-8)" >> $L
source $TC/openxc7/export.sh >/dev/null 2>&1
( cd $W/cells && env TC=$TC BDC_AUTO=1 BDC_AUTO_REWRITES=0 $XE NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 \
    BD_SIZES=$W/$Z PNR_TIMEOUT=7200 ./hw/build_bench.sh $K ) > /root/t186_${HALF}_build.log 2>&1
echo "build rc=$?" >> $L
D=$W/cells/build/hw/$T; O=/root/t186_out/$HALF; rm -rf $O; mkdir -p $O
echo "sdf $(md5sum < $D/$T.sdf | cut -c1-8) (spec $WS); untrimmed fasm $(md5sum < $D/$T.fasm | cut -c1-8)" >> $L
if [ "$TR" != - ]; then
  ( cd $W && env $XE python3 research/tools/auto/trim_lines.py --partial $D/${T}_routed.json $D/$T.fasm $O/${T}_routed.json $O/$T.fasm $(cat $W/$TR) ) > $O/trim.log 2>&1
  echo "trim rc=$?; recorded trims $(wc -l < $W/$TR); REFUSED $(grep -c '^REFUSED' $O/trim.log)" >> $L
  # control: the same trims WITHOUT the spec ENV (the old board_rebuild.sh behaviour)
  mkdir -p $O/noenv; ( cd $W && python3 research/tools/auto/trim_lines.py --partial $D/${T}_routed.json $D/$T.fasm $O/noenv/${T}_routed.json $O/noenv/$T.fasm $(cat $W/$TR) ) > $O/noenv/trim.log 2>&1
  echo "control no-ENV trim: REFUSED $(grep -c '^REFUSED' $O/noenv/trim.log); fasm $(md5sum < $O/noenv/$T.fasm | cut -c1-8)" >> $L
else cp $D/$T.fasm $O/$T.fasm; cp $D/${T}_routed.json $O/; fi
echo "trimmed fasm $(md5sum < $O/$T.fasm | cut -c1-8) (spec $WF); diff lines $(diff <(sort $D/$T.fasm) <(sort $O/$T.fasm) | grep -c '^[<>]'), non-INIT $(diff <(sort $D/$T.fasm) <(sort $O/$T.fasm) | grep '^[<>]' | grep -vc INIT)" >> $L
cp $D/$T.sdf $O/; cp $D/$T.fasm $O/untrimmed.fasm
PYTHONPATH=$TC/openxc7-src/prjxray:$TC/openxc7/lib/python python3 $TC/openxc7-src/prjxray/utils/fasm2frames.py --db-root $PDB --part $PART $O/$T.fasm > $O/$T.frames 2>$O/frames.log
$TC/openxc7/bin/xc7frames2bit --part_file $PDB/$PART/part.yaml --part_name $PART --frm_file $O/$T.frames --output_file $O/$T.bit > $O/bit.log 2>&1
echo "bit $(md5sum < $O/$T.bit | cut -c1-8)" >> $L
python3 $A/t67/scan_ff_own.py $O/$T.fasm > $O/ff.txt 2>&1; echo "ff: $(tail -1 $O/ff.txt)" >> $L
echo DONE >> $L
