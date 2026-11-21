#!/bin/bash
#CLUSTER array=1 cores=8 mem=32G time=90
# Shard C: item 30 (collatz64 h4s3 s10, sdf 637ff02e) fails 5/32 of research's draws in formal's simx (c_draws4):
# after n = 1 (answer 0), n = 97 returns 0. Which band class matters, which host / filter, and where the failing draw
# first parts from a passing variant (diverge.py, with the routed cell names).
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
K=collatz64; MLIR=research/data/fifteen/collatz64_preeq2.mlir; SZ=research/data/collatz64_sizes_T4cdb_h4s3_bench.vh; SEED=10
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $COL NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
B=$R/cells/build/hw/${K}_bench_gen; md5sum $B/${K}_bench_gen.sdf > $OUT/build.txt
W=$RUNS/m; mkdir -p $W
DRAWS=1 DRAW_SEED0=5 DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="27,27 1,1 97,97" TFULL=25000000 LATCH=1 \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
cp $W/draws.txt $OUT/draws_setup.txt
X="$W/simx $W/net.simx --periodic --maxev 100000000 --kernel collatz64 --corner 0 --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq --tmax 25000000 --draw 5 --gclass $W/gclass.txt --sreg 0.02 --sarc 0.126"
BD="0.216531,0.225189,0.986890"   # draw 5's research bands (b_c, b_r, b_cells)
v() { # label pairs bands extra...
  local L=$1 P=$2 BB=$3; shift 3
  local WANT=$(python3 formal/tools/margin/kernels.py collatz64 $P)
  echo "=== $L | pairs $P | bands $BB | $*" >> $OUT/runs.txt
  $X --want $WANT --pairs $P --bands $BB "$@" --dump $RUNS/$L.json 2>&1 | grep -E "^(RESULT|out0|simx: MAXEV)" | tee $RUNS/$L.res >> $OUT/runs.txt; }
v asis "27,27 1,1 97,97" $BD --hostdelay 12000 --w 20
v chain27 "27,27 1,1 97,97" 0.27,0.225189,0.986890 --hostdelay 12000 --w 20
v cells60 "27,27 1,1 97,97" 0.216531,0.225189,0.60 --hostdelay 12000 --w 20
v rest27 "27,27 1,1 97,97" 0.216531,0.27,0.986890 --hostdelay 12000 --w 20
v nopip "27,27 1,1 97,97" $BD --hostdelay 12000 --w 20 --sarc 0
v w0 "27,27 1,1 97,97" $BD --hostdelay 12000
v host1 "27,27 1,1 97,97" $BD --hostdelay 1 --w 20
v host100ns "27,27 1,1 97,97" $BD --hostdelay 100000 --w 20
v only97 "97,97" $BD --hostdelay 12000 --w 20
v n1then97 "1,1 97,97" $BD --hostdelay 12000 --w 20
v n27then97 "27,27 97,97" $BD --hostdelay 12000 --w 20
v n2then97 "2,2 97,97" $BD --hostdelay 12000 --w 20
for c in 0.40 0.50 0.70 0.80 0.90; do v cells$c "27,27 1,1 97,97" 0.216531,0.225189,$c --hostdelay 12000 --w 20; done
for L in cells60 chain27 rest27 nopip cells0.80 cells0.70 cells0.50 cells0.40 host100ns; do
  if grep -q "RESULT OK" $RUNS/$L.res 2>/dev/null && grep -q "RESULT MISMATCH" $RUNS/asis.res; then
    python3 formal/tools/margin/diverge.py $W/net.json $RUNS/asis.json $RUNS/$L.json --routed $W/routed.json --top 60 > $OUT/diverge_$L.txt 2>&1
  fi
done
exit 0
