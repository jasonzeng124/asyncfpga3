#!/bin/bash
#CLUSTER array=1-8 cores=8 mem=32G time=180
# Shard C (c_draws35): research's BOARD-QUEUE item 35 (xorshift, item 33's sizes x0.55 except UADDI0 = fr4a_x55a, seed 21,
# research's sdf 9145cd49) in formal's simx with research's draw model and xor19, fixed host 12 ns. Task 1: research's own
# draw numbers K = 2101..2132 (its draws2), draw for draw. Tasks 2-8: formal's draws 1..896 (128 each), for a pass fraction
# with a usable confidence interval. Formal's decode keeps FFs opaque (C23): FF-mux defects are invisible here.
set -uo pipefail
R=$PEER
SEED=21; F=55a
K=xorshift; MLIR=research/data/fifteen/xorshift_predec.mlir; SZ=research/data/xorshift_sizes_T3s50_fr4a_x${F}_bench.vh
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
echo "item35 x${F} seed $SEED sizes $SZ task $TASK" > $OUT/build.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $XOR BDC_FORK_OUT_LINK=n11__0 NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
tail -3 $RUNS/build.log >> $OUT/build.txt
B=$R/cells/build/hw/${K}_bench_gen; md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt 2>&1
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' $R/research/data/eventgraph/gate/xor19.hex)
if [ $TASK -eq 1 ]; then N=32; S0=2101; else N=128; S0=$(( (TASK-2)*128 + 1 )); fi
W=$RUNS/m; mkdir -p $W
DRAWS=$N DRAW_SEED0=$S0 DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="$PAIRS" TFULL=400000000 LATCH=1 JOBS=8 \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
for f in draws.txt draws_summary.txt md5.txt; do [ -f $W/$f ] && cp $W/$f $OUT/; done
exit 0
