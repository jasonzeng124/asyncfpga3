#!/bin/bash
#CLUSTER array=1-6 cores=8 mem=32G time=180
# Shard C, research's FOR-FORMAL 5feabe72 (board candidates 29-32; item 31 = fcsel3a s20 is C15): items 32 (collatz64 h4s3p s22),
# 30 (collatz64 h4s3 s10), 29 (ipow h4s3 s19) with the 1-ps host and the 12-ns host; all race classes, explained at the SDF.
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
CP="K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; KN=\"$COL\"; KER=collatz; PAIRS=\"27,27 703,703 77031,77031\""
HD=12000
C64="K=collatz64; MLIR=research/data/fifteen/collatz64_preeq2.mlir; KN=\"$COL\"; KER=collatz64; PAIRS=\"27,27 703,703 77031,77031\""
IPW="K=ipow; MLIR=; KN=\"BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0\"; KER=ipow; PAIRS=\"3,7 7,7 5,13 3,5\""
case $TASK in
1) NAME=item32_c64_s22_h1; eval "$C64"; SZ=research/data/collatz64_sizes_T4cdb_h4s3p_bench.vh; SEED=22; HD=1;;
2) NAME=item32_c64_s22; eval "$C64"; SZ=research/data/collatz64_sizes_T4cdb_h4s3p_bench.vh; SEED=22;;
3) NAME=item30_c64_s10; eval "$C64"; SZ=research/data/collatz64_sizes_T4cdb_h4s3_bench.vh; SEED=10;;
4) NAME=item29_ipow_s19; eval "$IPW"; SZ=research/data/ipow_dsp1_sizes_T9s75_h4s3_bench.vh; SEED=19;;
5) NAME=item30_c64_s10_h1; eval "$C64"; SZ=research/data/collatz64_sizes_T4cdb_h4s3_bench.vh; SEED=10; HD=1;;
6) NAME=item29_ipow_s19_h1; eval "$IPW"; SZ=research/data/ipow_dsp1_sizes_T9s75_h4s3_bench.vh; SEED=19; HD=1;;
esac
echo "$NAME hostdelay=$HD K=$K seed=$SEED sizes=$SZ mlir=$MLIR knobs=$KN" > $OUT/build.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/ 2>>$OUT/build.txt
[ -n "$MLIR" ] && cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $KN NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
tail -20 $RUNS/build.log >> $OUT/build.txt
echo "usinkeq2 count: $(grep -c usinkeq2 $R/cells/build/gen/${K}_kernel_bench.v)" >> $OUT/build.txt
B=$R/cells/build/hw/${K}_bench_gen
md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt 2>&1
W=$RUNS/m; mkdir -p $W
HOSTDELAY=$HD SDF=$B/${K}_bench_gen.sdf CONES=1 STEER=1 SIM=simx KERNEL=$KER PAIRS="$PAIRS" TFULL=25000000 LATCH=1 W0=1 KLO=0.0 JOBS=${JOBS:-8} \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
rc=$?
for f in fbslack.txt fbslack_ctl.txt cones.json names.txt arbs.json kappa_hi.txt checked.txt margins.txt summary.txt md5.txt run.log bnd.json; do [ -f $W/$f ] && cp $W/$f $OUT/; done
cp $W/explain_*.txt $OUT/ 2>/dev/null; [ -d $W/witness ] && { mkdir -p $OUT/witness; cp $W/witness/*.txt $W/witness/*.json $OUT/witness/ 2>/dev/null; }
exit $rc
