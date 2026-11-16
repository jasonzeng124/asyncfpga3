#!/bin/bash
#CLUSTER array=1-9 cores=8 mem=32G time=120
# Shard C: CAPTURE races (formal/tools/margin/cones.py: per latch group, the whole data cone into the latch bits slow, mux
# select routes included; everything else fast) on item 28 (fcsel3m s20), item 25, the shortened-select routes where research's
# rule E is negative (fcsel0 s24, fcsel1 s24: expected to fail lower = positive controls), fcsel2 s1, fcsel3m s1/s2, item 26, item 27.
# Rebuilt from $PEER (claude/research) with BOARD-QUEUE section 29's command, then formal/tools/margin/run.sh (bench mode, SIM=simx, latch pins, w 20 and 0).
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
CP="K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; KN=\"$COL\"; KER=collatz; PAIRS=\"27,27 703,703 77031,77031\""
case $TASK in
1) NAME=item28_fcsel3m_s20; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh; SEED=20;;
2) NAME=item25_collatz_s24; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl4_bench.vh; SEED=24;;
3) NAME=fcsel0_s24; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s0_bench.vh; SEED=24;;
4) NAME=fcsel1_s24; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s1_bench.vh; SEED=24;;
5) NAME=fcsel2_s1; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s2_bench.vh; SEED=1;;
6) NAME=fcsel3m_s1; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh; SEED=1;;
7) NAME=fcsel3m_s2; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh; SEED=2;;
8) NAME=item26_collatz64_s25; K=collatz64; MLIR=research/data/fifteen/collatz64_preeq2.mlir; KN="$COL"; SZ=research/data/collatz64_sizes_T4cdb_h2_bench.vh; SEED=25; KER=collatz64; PAIRS="27,27 703,703 77031,77031";;
9) NAME=item27_xorshift_s2; K=xorshift; MLIR=research/data/fifteen/xorshift_predec.mlir; KN="$XOR BDC_FORK_OUT_LINK=n11__0"; SZ=research/data/xorshift_sizes_T3s50_fr4_bench.vh; SEED=2; KER=xorshift; PAIRS="0x92d68ca2,3 0x92d68ca2,4 0x92d68ca2,8 0x92d68ca2,5";;
esac
echo "$NAME K=$K seed=$SEED sizes=$SZ mlir=$MLIR knobs=$KN" > $OUT/build.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/ 2>>$OUT/build.txt
[ -n "$MLIR" ] && cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $KN NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
tail -20 $RUNS/build.log >> $OUT/build.txt
echo "usinkeq2 count: $(grep -c usinkeq2 $R/cells/build/gen/${K}_kernel_bench.v)" >> $OUT/build.txt
B=$R/cells/build/hw/${K}_bench_gen
md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt 2>&1
W=$RUNS/m; mkdir -p $W
CONES=only SIM=simx KERNEL=$KER PAIRS="$PAIRS" TFULL=25000000 LATCH=1 W0=1 KLO=0.0 JOBS=${JOBS:-8} \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
rc=$?
for f in cones.json names.txt arbs.json kappa_hi.txt checked.txt margins.txt summary.txt md5.txt run.log bnd.json; do [ -f $W/$f ] && cp $W/$f $OUT/; done
[ -d $W/witness ] && { mkdir -p $OUT/witness; cp $W/witness/*.txt $W/witness/*.json $OUT/witness/ 2>/dev/null; }
exit $rc
