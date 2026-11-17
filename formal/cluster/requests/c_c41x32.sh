#!/bin/bash
#CLUSTER array=1-32 cores=4 mem=16G time=240
# Shard C (c_c41x32): research's cand3b in formal's simx -- item 35's sizes with UCMPI0 6 -> 10 (C41; research/data/
# xorshift_sizes_T3s50_fr4a_x55a10_bench.vh), route = TASK (seeds 1-32). Per route: build (research's flow), 4 default draws
# K = 100S+1..4 and 4 slow-carry draws K = 100S+51..54 with CARRY/F7/FF in [0.8, 1.0] (DRAW_XBAND, = research's DRAW_CARRY
# draw for draw), then loop-steer settle margins (steercorners.sh) at chains 0.20, CARRY 1.0, rest 0.31 / 0.20.
set -uo pipefail
export RC_TREE=1   # formal arcs with the RC tree (A18; default arcs ~20 % fast)
R=$PEER; S=$TASK; K=xorshift
SZ=research/data/xorshift_sizes_T3s50_fr4a_x55a10_bench.vh
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0"
echo "x55a10 seed $S" > $OUT/build.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
cp $R/research/data/fifteen/xorshift_predec.mlir $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $XOR NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
B=$R/cells/build/hw/${K}_bench_gen; md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt 2>&1
G=$R/research/data/eventgraph/gate; V=formal/tools/margin/vec/xorlong.hex
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' $G/xor19.hex)
W=$RUNS/m; mkdir -p $W
run() { DRAWS=4 DRAW_SEED0=$1 DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="$PAIRS" TFULL=1500000000 LATCH=1 JOBS=$JOBS \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run_$1.txt 2>&1
  cp $W/draws_summary.txt $OUT/draws_summary_$1.txt; cp $W/draws.txt $OUT/draws_$1.txt; }
run $((100*S+1))
export DRAW_XBAND=0.8,1.0; run $((100*S+51)); unset DRAW_XBAND
cat $G/xor19.hex $V > $RUNS/vec.hex
bash formal/tools/margin/steercorners.sh $W $K $RUNS/vec.hex "0.20,0.31,1.0 0.20,0.20,1.0" 'ucmpi0\.uz_n3$' 'ucmpi1\.uz_n41$' > $OUT/steer.txt 2>&1
exit 0
