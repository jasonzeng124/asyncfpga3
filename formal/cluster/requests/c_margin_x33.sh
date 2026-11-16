#!/bin/bash
#CLUSTER array=1-8 cores=8 mem=32G time=180
# Shard C, research FOR-FORMAL (item 33 = xorshift fr4a seed 27, sdf 7f0c0592): its margin and binding race with the
# 12-ns, 1-ps and 2-ns hosts; the same design on 4 more routes (seeds 1 3 4 5, host 2 ns); item 27 s2 under the SAME
# settings (host 2 ns) beside it. All race classes, every race explained at the SDF.
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
CP="K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; KN=\"$COL\"; KER=collatz; PAIRS=\"27,27 703,703 77031,77031\""
XK="K=xorshift; MLIR=research/data/fifteen/xorshift_predec.mlir; KER=xorshift; PAIRS=\"0x92d68ca2,3 0x92d68ca2,4 0x92d68ca2,8 0x92d68ca2,5\""
SZA=research/data/xorshift_sizes_T3s50_fr4a_bench.vh
HD=2000
case $TASK in
1) NAME=item33_s27; SEED=27; SZ=$SZA; HD=12000;;
2) NAME=item33_s27_h1; SEED=27; SZ=$SZA; HD=1;;
3) NAME=item33_s27_h2; SEED=27; SZ=$SZA;;
4|5|6|7) SEED=$(echo 1 3 4 5 | cut -d' ' -f$((TASK-3))); NAME=x33_s$SEED; SZ=$SZA;;
8) NAME=item27_s2_h2; SEED=2; SZ=research/data/xorshift_sizes_T3s50_fr4_bench.vh;;
esac
eval "$XK"; KN="$XOR BDC_FORK_OUT_LINK=n11__0"
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
