#!/bin/bash
#CLUSTER array=1-32 cores=4 mem=16G time=240
# Shard C (c_half16): FOR-RESEARCH C51 on more routes. collatz x0.70 (tasks 1-16 = seeds 1-16) and ipow x0.70 (tasks 17-32 =
# seeds 1-16), research's sizes files and flows (shrink9 / shrink8). Per route: RC_TREE decode, 8 draws of research's model
# (K 100S+1..8) unscaled, then the same 8 draws with every non-compare matched-delay chain's routed path at 0.5x
# (chainscale.py --joint ucmpi --emit-inject 0.5), and chainscale --only ucmpi at the two fast-chain corners.
set -uo pipefail
export RC_TREE=1
R=$PEER; T=$TASK; S=$(( (T-1) % 16 + 1 ))
if [ $T -le 16 ]; then K=collatz; Z=research/data/collatz_sizes_T3cdb_nl6s3a_x70_bench.vh; V=col18
  KN="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"; M=research/data/fifteen/collatz_preeq2.mlir
else K=ipow; Z=research/data/ipow_dsp1_sizes_T9s75_h4s3m_x70_bench.vh; V=ipow17
  KN="BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"; M=; fi
echo "$K x0.70 seed $S" > $OUT/build.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
[ -n "$M" ] && cp $R/$M $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $KN NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$Z ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
B=$R/cells/build/hw/${K}_bench_gen; md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt 2>&1
G=$R/research/data/eventgraph/gate; PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' $G/$V.hex)
W=$RUNS/m; mkdir -p $W
run() { DRAWS=8 DRAW_SEED0=$((100*S+1)) DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="$PAIRS" TFULL=1500000000 LATCH=1 JOBS=$JOBS \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run_$1.txt 2>&1
  cp $W/draws_summary.txt $OUT/draws_summary_$1.txt; cp $W/draws.txt $OUT/draws_$1.txt; }
run plain
python3 formal/tools/margin/chainscale.py $W --kernel $K --pairs $PAIRS --only udut --joint ucmpi --emit-inject 0.5 $RUNS/inj.json > $OUT/inj.txt 2>&1
export DRAW_INJECT=$RUNS/inj.json; run half; unset DRAW_INJECT
python3 formal/tools/margin/chainscale.py $W --kernel $K --pairs $PAIRS --only ucmpi --jobs $JOBS > $OUT/cmp.txt 2>&1
exit 0
