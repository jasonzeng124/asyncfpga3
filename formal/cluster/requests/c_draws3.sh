#!/bin/bash
#CLUSTER array=1-6 cores=16 mem=64G time=240
# Shard C: research's draws1 mirrored in formal's simulator of the decoded bitstream, for the owner's disagreement table
# (research FOR-FORMAL 2026-11-16 evening). Same route (built by research's own eval_task.sh, STATIC_ONLY=1, as draws1
# does, BD_SKEW_AND_JOIN=1 and MLIR_OVERRIDE included), same draws K = 1..32 (bands from Random(7919K+17); region 0.02;
# per-pip 0.126), same gate vectors. Differences: formal's transport LUTs with H_RUNT(20) (no resolver), host 12 ns
# after each acknowledge, start-up = formal's. ipow (item 29) is not decodable (DSP48E1): skipped.
set -uo pipefail
F=$(pwd)
G=research/data/eventgraph/gate
XENV="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0"
CENV="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
case $TASK in
  1) N=fxa; K=xorshift; S=27; Z=research/data/xorshift_sizes_T3s50_fr4a_bench.vh; V=xor19; E=$XENV;;
  2) N=fxd; K=xorshift; S=2; Z=research/data/xorshift_sizes_T3s50_fr4_bench.vh; V=xor19; E=$XENV;;
  3) N=fcsel3a; K=collatz; S=20; Z=research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh; V=col14; E=$CENV;;
  4) N=fcsel3m; K=collatz; S=20; Z=research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh; V=col14; E=$CENV;;
  5) N=fc64sel3; K=collatz64; S=10; Z=research/data/collatz64_sizes_T4cdb_h4s3_bench.vh; V=c6415; E=$CENV;;
  6) N=fc64sel3p; K=collatz64; S=22; Z=research/data/collatz64_sizes_T4cdb_h4s3p_bench.vh; V=c6415; E=$CENV;;
esac
case $K in xorshift) export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir;;
           collatz|collatz64) export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/${K}_preeq2.mlir;; esac
NM=dr_${N}_$S; export RUNS
echo "$N kernel $K seed $S vectors $V (research draws1 candidate)" > $OUT/build.txt
( cd $PEER && STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $S research/data/fifteen/vec_${K%64}.hex $G/$V.hex $G/$V.exp $E ) > $RUNS/eval.log 2>&1
HW=$RUNS/hw/$NM; D=${K}_bench_gen
ls $HW >> $OUT/build.txt; md5sum $HW/$D.sdf $HW/$D.fasm $RUNS/r/$NM/xray.sdf >> $OUT/build.txt 2>&1
tail -5 $RUNS/eval.log >> $OUT/build.txt
BV=$HW/$D.v; [ -f "$BV" ] || BV=$PEER/cells/build/gen/$D.v
KV=$HW/${K}_kernel_bench.v; [ -f "$KV" ] || KV=$PEER/cells/build/gen/${K}_kernel_bench.v
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' $PEER/$G/$V.hex)
W=$RUNS/m; mkdir -p $W
cd $F
DRAWS=32 DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="$PAIRS" TFULL=400000000 LATCH=1 JOBS=${JOBS:-16} \
  SYNTH=$HW/$D.json ROUTED=$HW/${D}_routed.json KV=$KV BV=$BV bash formal/tools/margin/run.sh $HW/$D.fasm $W > $OUT/run.txt 2>&1
rc=$?
for f in draws.txt draws_summary.txt md5.txt run.log; do [ -f $W/$f ] && cp $W/$f $OUT/; done
exit $rc
