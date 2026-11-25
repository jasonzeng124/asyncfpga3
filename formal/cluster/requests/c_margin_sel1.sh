#!/bin/bash
#CLUSTER array=1-6 cores=8 mem=32G time=150
# Shard C: research's shortened-select collatz builds (FOR-FORMAL: item 25's command, select links ulink_n14__0/1, ulink_n_index_11 at DELAY 0/1/2 = nl6s0/1/2) rebuilt from $PEER (claude/research) with the commands in
# research/FOR-FORMAL.md, then formal/tools/margin/run.sh (bench mode, SIM=simx, latch pins, w 20 and 0).
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
case $TASK in
1) NAME=fcsel2_s1; SEED=1; S=2;;
2) NAME=fcsel2_s2; SEED=2; S=2;;
3) NAME=fcsel1_s24; SEED=24; S=1;;
4) NAME=fcsel0_s24; SEED=24; S=0;;
5) NAME=fcsel2_s24; SEED=24; S=2;;
6) NAME=fcsel1_s1; SEED=1; S=1;;
esac
K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; KN="$COL"; SZ=research/data/collatz_sizes_T3cdb_nl6s${S}_bench.vh; KER=collatz; PAIRS="27,27 703,703 77031,77031"

echo "$NAME K=$K seed=$SEED sizes=$SZ mlir=$MLIR knobs=$KN" > $OUT/build.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/ 2>>$OUT/build.txt
[ -n "$MLIR" ] && cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $KN NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
tail -20 $RUNS/build.log >> $OUT/build.txt
B=$R/cells/build/hw/${K}_bench_gen
md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt 2>&1
W=$RUNS/m; mkdir -p $W
SIM=simx KERNEL=$KER PAIRS="$PAIRS" TFULL=25000000 LATCH=1 W0=1 KLO=0.0 JOBS=${JOBS:-8} \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
rc=$?
for f in names.txt arbs.json kappa_hi.txt checked.txt margins.txt summary.txt md5.txt run.log bnd.json; do [ -f $W/$f ] && cp $W/$f $OUT/; done
[ -d $W/witness ] && { mkdir -p $OUT/witness; cp $W/witness/*.txt $W/witness/*.json $OUT/witness/ 2>/dev/null; }
exit $rc
