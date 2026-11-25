#!/bin/bash
#CLUSTER array=1,3-5 cores=8 mem=32G time=150
# Shard C (rerun of c_margin_bench1 tasks 1,3-5 with arbiters named (ArbOK checked) and instance names (names.txt)): research's FOR-FORMAL bench builds rebuilt from $PEER (claude/research) with the commands in
# research/FOR-FORMAL.md, then formal/tools/margin/run.sh (bench mode, SIM=simx, latch pins, w 20 and 0).
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
case $TASK in
1) NAME=item25_collatz_s24; K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; KN="$COL"; SZ=research/data/collatz_sizes_T3cdb_nl4_bench.vh; SEED=24; KER=collatz; PAIRS="27,27 703,703 77031,77031";;
2) NAME=item27_xorshift_s2; K=xorshift; MLIR=research/data/fifteen/xorshift_predec.mlir; KN="$XOR BDC_FORK_OUT_LINK=n11__0"; SZ=research/data/xorshift_sizes_T3s50_fr4_bench.vh; SEED=2; KER=xorshift; PAIRS="0x92d68ca2,3 0x92d68ca2,4 0x92d68ca2,8 0x92d68ca2,5";;
3) NAME=item26_collatz64_s25; K=collatz64; MLIR=research/data/fifteen/collatz64_preeq2.mlir; KN="$COL"; SZ=research/data/collatz64_sizes_T4cdb_h2_bench.vh; SEED=25; KER=collatz64; PAIRS="27,27 703,703 77031,77031";;
4) NAME=BAD_nc64_7; K=collatz64; MLIR=; KN="BDC_CONST_DATA=1"; SZ=research/data/collatz64_sizes_T4cd_bench.vh; SEED=7; KER=collatz64; PAIRS="27,27 703,703 77031,77031";;
5) NAME=pc64_7; K=collatz64; MLIR=; KN="BDC_CONST_DATA=1"; SZ=research/data/fifteen/selectrule/collatz64_sizes_T4cd_sel19_bench.vh; SEED=7; KER=collatz64; PAIRS="27,27 703,703 77031,77031";;
esac
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
