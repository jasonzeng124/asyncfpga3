#!/bin/bash
#CLUSTER array=1 cores=8 mem=32G time=120
# Shard C (c_margin_usel2 + conenames.py: which cones pass through uselect0, and their results), research's ask "a margin at uselect0's line (its data vs its request)" on fcsel3a seed 20 (sdf 7aefc4bd): every
# latch-group capture cone (CONES=only) swept up to kappa 0.90 with the 12 ns host, each failure explained in ps at the SDF.
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
CP="K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; KN=\"$COL\"; KER=collatz; PAIRS=\"27,27 703,703 77031,77031\""
HD=12000
case $TASK in
1) NAME=fcsel3a_s20_cones; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh; SEED=20;;
esac
echo "$NAME hostdelay=$HD K=$K seed=$SEED sizes=$SZ mlir=$MLIR knobs=$KN" > $OUT/build.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/ 2>>$OUT/build.txt
[ -n "$MLIR" ] && cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $KN NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
tail -20 $RUNS/build.log >> $OUT/build.txt
echo "usinkeq2 count: $(grep -c usinkeq2 $R/cells/build/gen/${K}_kernel_bench.v)" >> $OUT/build.txt
B=$R/cells/build/hw/${K}_bench_gen
md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt 2>&1
W=$RUNS/m; mkdir -p $W
HOSTDELAY=$HD SDF=$B/${K}_bench_gen.sdf EXPLAIN_ALL=1 KHI=0.90 CONES=only SIM=simx KERNEL=$KER PAIRS="$PAIRS" TFULL=25000000 LATCH=1 W0=1 KLO=0.30 JOBS=${JOBS:-8} \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
rc=$?
for f in cones_named.txt fbslack.txt fbslack_ctl.txt cones.json names.txt arbs.json kappa_hi.txt checked.txt margins.txt summary.txt md5.txt run.log bnd.json; do [ -f $W/$f ] && cp $W/$f $OUT/; done
cp $W/explain_*.txt $OUT/ 2>/dev/null; [ -d $W/witness ] && { mkdir -p $OUT/witness; cp $W/witness/*.txt $W/witness/*.json $OUT/witness/ 2>/dev/null; }
exit $rc
