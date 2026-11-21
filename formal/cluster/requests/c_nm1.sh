#!/bin/bash
#CLUSTER array=1-3 cores=8 mem=32G time=120
# Shard C (c_nm1): first use of simx's NEARMISS line (narrowest pulse on a storage-LUT output per run, informational).
# Does it separate draws that pass near a failure from draws far from one? Task 1: collatz x0.40 route 20 (C26: 10/19/3 of
# 32); task 2: xorshift x0.50a route 18 (C25: fails draws 4, 5, 10, 12, 21); task 3: item 35 (x0.55a route 21; all pass so
# far). Research's model, draws 1-32, fixed host 12 ns.
# RACES=1: simx also reports the closest input reorderings (gap ps) at storage LUTs and LUTs feeding them.
set -uo pipefail
R=$PEER
case $TASK in
1) K=collatz; SEED=20; SZ=research/data/collatz_sizes_T3cdb_nl6s3a_fx40_bench.vh; V=col14; MLIR=research/data/fifteen/collatz_preeq2.mlir
   python3 $R/research/tools/shrink_sizes.py $R/research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh 0.40 $R/$SZ > $OUT/shrink.txt 2>&1
   KN="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0";;
2|3) K=xorshift; V=xor19; MLIR=research/data/fifteen/xorshift_predec.mlir
   [ $TASK = 2 ] && { SEED=18; SZ=research/data/xorshift_sizes_T3s50_fr4a_x50a_bench.vh; } || { SEED=21; SZ=research/data/xorshift_sizes_T3s50_fr4a_x55a_bench.vh; }
   KN="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_FORK_OUT_LINK=n11__0";;
esac
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $KN NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
B=$R/cells/build/hw/${K}_bench_gen; echo "$K $SZ route $SEED" > $OUT/build.txt; md5sum $B/${K}_bench_gen.sdf >> $OUT/build.txt
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' $R/research/data/eventgraph/gate/$V.hex)
W=$RUNS/m; mkdir -p $W
RACES=1 DRAWS=32 DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="$PAIRS" TFULL=400000000 LATCH=1 JOBS=8 \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
for f in draws.txt draws_summary.txt; do [ -f $W/$f ] && cp $W/$f $OUT/; done
exit 0
