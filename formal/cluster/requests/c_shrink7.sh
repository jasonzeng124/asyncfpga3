#!/bin/bash
#CLUSTER array=1-64 cores=8 mem=32G time=240
# Shard C (c_shrink7): research's shrink7 in formal's simx: collatz item 31's sizes (nl6s3a) x0.55 (tasks 1-32) and x0.70
# (tasks 33-64) of EVERY size, routes 1-32, vectors col17 (col14 + n = 77671, 94959, 109881: 31-bit trajectory peaks, so
# the long carries are simulated). Research's model; research's draw numbers K = 100*route + 1..4 (draw for draw), then
# formal's draws 1..28. Fixed host 12 ns. FFs opaque in formal's decode (C23).
set -uo pipefail
R=$PEER
FS=(55 70); F=${FS[$(( (TASK-1) / 32 ))]}; SEED=$(( (TASK-1) % 32 + 1 ))
K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; SZ=research/data/collatz_sizes_T3cdb_nl6s3a_x${F}_bench.vh
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
echo "s7_x${F}_$SEED factor $F seed $SEED sizes $SZ" > $OUT/build.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $COL NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
B=$R/cells/build/hw/${K}_bench_gen; md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt 2>&1
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' $R/research/data/eventgraph/gate/col17.hex)
W=$RUNS/m; mkdir -p $W
go() { DRAWS=$1 DRAW_SEED0=$2 DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="$PAIRS" TFULL=800000000 LATCH=1 JOBS=8 \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W; }
go 4 $((SEED*100+1)) > $OUT/run.txt 2>&1
for f in draws.txt draws_summary.txt; do [ -f $W/$f ] && mv $W/$f $OUT/rk_$f; done
go 28 1 > $OUT/run2.txt 2>&1
for f in draws.txt draws_summary.txt md5.txt; do [ -f $W/$f ] && cp $W/$f $OUT/own_$f; done
exit 0
