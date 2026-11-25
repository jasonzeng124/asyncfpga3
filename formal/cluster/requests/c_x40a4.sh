#!/bin/bash
#CLUSTER array=1 cores=8 mem=32G time=90
# Shard C: name the race that fails item 33 x0.40a on route 4 (0/32 draws in formal, C24): draw 1 as drawn, each band
# class moved, and the LUTs whose flip count differs from a passing variant (diverge.py, routed names).
set -uo pipefail
R=$PEER
K=xorshift; MLIR=research/data/fifteen/xorshift_predec.mlir; SZ=research/data/xorshift_sizes_T3s50_fr4a_x40a_bench.vh; SEED=4
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $XOR BDC_FORK_OUT_LINK=n11__0 NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
B=$R/cells/build/hw/${K}_bench_gen; md5sum $B/${K}_bench_gen.sdf > $OUT/build.txt
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' $R/research/data/eventgraph/gate/xor19.hex)
W=$RUNS/m; mkdir -p $W
DRAWS=1 DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="$PAIRS" TFULL=400000000 LATCH=1 \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
cp $W/draws.txt $OUT/
WANT=$(python3 formal/tools/margin/kernels.py xorshift $PAIRS)
X="$W/simx $W/net.simx --periodic --maxev 1000000000 --kernel xorshift --want $WANT --pairs $PAIRS --corner 0 --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq --tmax 400000000 --hostdelay 12000 --draw 1 --gclass $W/gclass.txt --sreg 0.02 --sarc 0.126 --w 20"
v() { L=$1; shift; echo "=== $L | $*" >> $OUT/runs.txt; $X "$@" --dump $RUNS/$L.json > $RUNS/$L.out 2>&1; grep -E "^RESULT|MAXEV" $RUNS/$L.out | sed 's/want \[[^]]*\]//' | cut -c1-250 >> $OUT/runs.txt; grep "^out0" $RUNS/$L.out | head -8 >> $OUT/runs.txt; }
v asis --bands 0.269827,0.261244,0.765207
v chain31 --bands 0.31,0.261244,0.765207
v chain40 --bands 0.40,0.261244,0.765207
v rest20 --bands 0.269827,0.20,0.765207
v cells20 --bands 0.269827,0.261244,0.20
v cells100 --bands 0.269827,0.261244,1.0
v nopip --bands 0.269827,0.261244,0.765207 --sarc 0
for L in chain40 chain31 cells20 rest20 nopip; do
  if grep -q "RESULT OK" $RUNS/$L.out && grep -q "RESULT MISMATCH" $RUNS/asis.out; then
    python3 formal/tools/margin/diverge.py $W/net.json $RUNS/asis.json $RUNS/$L.json --routed $W/routed.json --top 40 | sed -n '/COUNT/,$p' > $OUT/diverge_$L.txt 2>&1; break; fi
done
exit 0
