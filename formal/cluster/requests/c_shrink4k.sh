#!/bin/bash
#CLUSTER array=17-48 cores=8 mem=32G time=120
# Shard C (c_shrink4k: x0.40a / x0.30a on routes 1-16 with research's OWN draw numbers K = route*100 + 1..4 as its
# shrink4, so the verdicts compare draw for draw). Was c_shrink34: research's shrink3 / shrink4 board-candidate sizes in formal's simx: x0.40c, x0.40a, x0.30a on
# routes 1-16 (tasks 1-48) and x0.30 / 0.20 / 0.10 on routes 2, 5 (tasks 49-54); research's model, draws 1-32 (research:
# 4 per route on 1-16, 8 on 2/5). Formal's decode keeps FFs opaque: FF-mux defects are invisible here (C23).
# Was: research's shrink1 mirrored in formal's simx (the second approximation PROGRAM asks for): item 33 (xorshift
# fr4a) with every matched delay scaled by 0.85 / 0.70 / 0.55 / 0.40 (research's sizes files), routes 27, 2, 5, 9;
# research's draw model, draws 1-64 (research runs 1-8), xor19, host 12 ns (fixed host). Task = factor x route as theirs.
set -uo pipefail
R=$PEER
if [ $TASK -le 48 ]; then FS=(40c 40a 30a); F=${FS[$(( (TASK-1) / 16 ))]}; SEED=$(( (TASK-1) % 16 + 1 ))
else FS=(30 30 20 20 10 10); SS=(2 5 2 5 2 5); F=${FS[$((TASK-49))]}; SEED=${SS[$((TASK-49))]}; fi
K=xorshift; MLIR=research/data/fifteen/xorshift_predec.mlir; SZ=research/data/xorshift_sizes_T3s50_fr4a_x${F}_bench.vh
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
echo "sh_x${F}_$SEED factor $F seed $SEED sizes $SZ" > $OUT/build.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $XOR BDC_FORK_OUT_LINK=n11__0 NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
tail -3 $RUNS/build.log >> $OUT/build.txt
B=$R/cells/build/hw/${K}_bench_gen; md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt 2>&1
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' $R/research/data/eventgraph/gate/xor19.hex)
W=$RUNS/m; mkdir -p $W
DRAWS=4 DRAW_SEED0=$((SEED*100+1)) DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="$PAIRS" TFULL=400000000 LATCH=1 JOBS=8 \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
for f in draws.txt draws_summary.txt md5.txt; do [ -f $W/$f ] && cp $W/$f $OUT/; done
exit 0
