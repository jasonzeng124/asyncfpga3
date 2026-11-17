#!/bin/bash
#CLUSTER array=1-16 cores=8 mem=32G time=180
# Shard C (c_shrink2b): where collatz item 31's sizes first fail in formal's simx: every size x0.40 / 0.30 / 0.20 / 0.10
# (research's shrink_sizes.py on nl6s3a, written into the task's own copy, as research would), routes 20, 3, 7, 12.
# Was: research's shrink2 (collatz item 31 sizes nl6s3a x0.85 / 0.70 / 0.55, routes 20, 3, 7, 12; tasks 1-12) in formal's
# simx, plus x0.55 on 4 more routes (1, 2, 4, 5; tasks 13-16). Research's model, draws 1-32 (research: 1-8), col14, fixed host.
set -uo pipefail
R=$PEER
FS=(40 30 20 10); SS=(20 3 7 12); F=${FS[$(( (TASK-1) / 4 ))]}; SEED=${SS[$(( (TASK-1) % 4 ))]}
K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; SZ=research/data/collatz_sizes_T3cdb_nl6s3a_fx${F}_bench.vh
python3 $R/research/tools/shrink_sizes.py $R/research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh 0.$F $R/$SZ > $OUT/shrink.txt 2>&1
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
echo "sc_x${F}_$SEED factor $F seed $SEED sizes $SZ" > $OUT/build.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $COL NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
B=$R/cells/build/hw/${K}_bench_gen; md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt 2>&1
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' $R/research/data/eventgraph/gate/col14.hex)
W=$RUNS/m; mkdir -p $W
DRAWS=32 DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="$PAIRS" TFULL=400000000 LATCH=1 JOBS=8 \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
for f in draws.txt draws_summary.txt md5.txt; do [ -f $W/$f ] && cp $W/$f $OUT/; done
exit 0
