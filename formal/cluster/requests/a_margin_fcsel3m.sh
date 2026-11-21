#!/bin/bash
#CLUSTER array=1-6 cores=8 mem=32G time=150
# Shard A (2026-11-16): research's collatz board candidate fcsel3m (BOARD-QUEUE item 28 / ## 29: select links at 3, nl6s3m sizes, seed 20, sdf d86bdde5) and four more of its seeds (1, 2, 7, 24; research gated 28 routes), beside item 25 (nl4, seed 24) under the SAME settings as C's c_margin_sel1 (C10). PROGRAM.md "Next for the margin tool" (02:55 UTC).
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
case $TASK in
1) NAME=fcsel3m_s20; SEED=20; S=3m;;
2) NAME=item25_s24_sel1set; SEED=24; S=4;;
3) NAME=fcsel3m_s1; SEED=1; S=3m;;
4) NAME=fcsel3m_s2; SEED=2; S=3m;;
5) NAME=fcsel3m_s24; SEED=24; S=3m;;
6) NAME=fcsel3m_s7; SEED=7; S=3m;;
esac
K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; KN="$COL"; SZ=research/data/collatz_sizes_T3cdb_nl6s${S}_bench.vh; [ "$S" = 4 ] && SZ=research/data/collatz_sizes_T3cdb_nl4_bench.vh; KER=collatz; PAIRS="27,27 703,703 77031,77031"

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
