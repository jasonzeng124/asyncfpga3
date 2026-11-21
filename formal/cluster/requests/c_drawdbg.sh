#!/bin/bash
#CLUSTER array=1 cores=8 mem=32G time=60
# Shard C: why c_draws1's collatz draws return nothing (64/64 "got []"): one build (item 25 s24), simx runs that
# separate the vector format (n,0 vs n,n), the draw model and the long tmax.
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; SZ=research/data/collatz_sizes_T3cdb_nl4_bench.vh; SEED=24
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $COL NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
B=$R/cells/build/hw/${K}_bench_gen; md5sum $B/${K}_bench_gen.sdf > $OUT/build.txt
W=$RUNS/m; mkdir -p $W
DRAWS=1 HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="27,27" TFULL=25000000 LATCH=1 \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
cp $W/bnd.json $OUT/ 2>/dev/null
X="$W/simx $W/net.simx --periodic --maxev 100000000 --hostdelay 12000 --kernel collatz --corner 0 --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq"
echo '{"S": [], "F": []}' > $RUNS/e.json
for v in "27,27|25000000|" "27,0|25000000|" "27,27|400000000|" "27,0|25000000|--draw 1" "27,27|25000000|--draw 1" "27,0|400000000|--draw 1" "1,0 27,0|25000000|--draw 1"; do
  IFS='|' read -r P T D <<< "$v"
  W2=$(python3 formal/tools/margin/kernels.py collatz $P)
  if [ -n "$D" ]; then A="$D"; else A="--kappa 0 --classes $RUNS/e.json --cdefault F"; fi
  echo "=== pairs $P tmax $T $A" >> $OUT/runs.txt
  $X --want $W2 --pairs $P --tmax $T $A --w 20 2>&1 | grep -vE "^(env|HRUNT)" | tail -8 >> $OUT/runs.txt
done
exit 0
