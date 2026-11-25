#!/bin/bash
#CLUSTER array=1-5 cores=8 mem=32G time=180
# Shard A (2026-11-16): the select-arrival sweep (formal/tools-A/target/selrun.sh: late inputs of combinational LUTs that
# feed storage, which C's run.sh does not list) on research's board candidates and on the collatz64 minimal pair whose
# only difference is a select link (nc64_7: ulink_n14__1 19 -> 10, BAD; pc64_7 GOOD). Builds from $PEER with
# research/FOR-FORMAL.md's commands (the lines are C's c_margin_bench3.sh); run.sh with TOP=1 only prepares the net and
# the reference dump. Then selrun at 0.45 (sel/) and the same candidates at 0.45-0.95 (sel95/).
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
case $TASK in
1) NAME=item27_xorshift_s2; K=xorshift; MLIR=research/data/fifteen/xorshift_predec.mlir; KN="$XOR BDC_FORK_OUT_LINK=n11__0"; SZ=research/data/xorshift_sizes_T3s50_fr4_bench.vh; SEED=2; KER=xorshift; PAIRS="0x92d68ca2,3 0x92d68ca2,4 0x92d68ca2,8 0x92d68ca2,5";;
2) NAME=item26_collatz64_s25; K=collatz64; MLIR=research/data/fifteen/collatz64_preeq2.mlir; KN="$COL"; SZ=research/data/collatz64_sizes_T4cdb_h2_bench.vh; SEED=25; KER=collatz64; PAIRS="27,27 703,703 77031,77031";;
3) NAME=BAD_nc64_7; K=collatz64; MLIR=; KN="BDC_CONST_DATA=1"; SZ=research/data/collatz64_sizes_T4cd_bench.vh; SEED=7; KER=collatz64; PAIRS="27,27 703,703 77031,77031";;
4) NAME=pc64_7; K=collatz64; MLIR=; KN="BDC_CONST_DATA=1"; SZ=research/data/fifteen/selectrule/collatz64_sizes_T4cd_sel19_bench.vh; SEED=7; KER=collatz64; PAIRS="27,27 703,703 77031,77031";;
5) NAME=item23_xorshift_s10; K=xorshift; MLIR=; KN="$XOR BDC_FORK_OUT_LINK=n11__0,n30__0"; SZ=research/data/xorshift_sizes_T3s50_fr3_bench.vh; SEED=10; KER=xorshift; PAIRS="0x92d68ca2,3 0x92d68ca2,4 0x92d68ca2,8 0x92d68ca2,5";;
esac
echo "$NAME K=$K seed=$SEED sizes=$SZ mlir=$MLIR knobs=$KN" > $OUT/build.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/ 2>>$OUT/build.txt
[ -n "$MLIR" ] && cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $KN NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
tail -5 $RUNS/build.log >> $OUT/build.txt
B=$R/cells/build/hw/${K}_bench_gen
md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt 2>&1
W=$RUNS/m; mkdir -p $W
export SIM=simx KERNEL=$KER PAIRS="$PAIRS" TFULL=25000000 LATCH=1 W0=1 KLO=0.0 JOBS=${JOBS:-8}
SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v TOP=1 bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/prep.txt 2>&1
# run.sh's bench branch can leave arbs.json = [] (arbs.py | head -1 under pipefail): regenerate it
python3 formal/tools-A/target/arbs.py $W/routed.json $W/d0.json $W/net.json $W/arbs.json >> $OUT/prep.txt 2>&1
KLO=0.20 bash formal/tools-A/target/selrun.sh $W > $OUT/sel.txt 2>&1
S=$W/sel95; mkdir -p $S; for f in net.json bnd.json arbs.json routed.json; do ln -sf $W/$f $S/$f; done
SIMX=$W/simx python3 formal/tools/margin/margin.py $S/net.json $S/bnd.json $W/sel/ranked.json $S --jobs $JOBS --khi 0.95 --klo 0.45 \
  --tfull 25000000 --pairs $PAIRS --kernel $KER --w 20 > $OUT/sel95.txt 2>&1
python3 formal/tools/margin/checkrows.py $S > /dev/null 2>&1; python3 formal/tools/margin/names.py $S > /dev/null 2>&1
for d in sel sel95; do mkdir -p $OUT/$d; for f in kappa_hi.txt checked.txt names.txt margins.txt summary.txt run.log sweep_w20.txt; do [ -f $W/$d/$f ] && cp $W/$d/$f $OUT/$d/; done
  [ -d $W/$d/witness ] && { mkdir -p $OUT/$d/witness; cp $W/$d/witness/*.txt $W/$d/witness/*.json $OUT/$d/witness/ 2>/dev/null; }; done
cp $W/md5.txt $W/arbs.json $OUT/ 2>/dev/null
exit 0
