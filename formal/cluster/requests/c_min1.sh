#!/bin/bash
#CLUSTER array=1-3 cores=8 mem=32G time=90
# Shard C: the steer-cone kernel races (host 2 ns) minimised (minimize.py) then explained and verified: item 27 (0.35 w0 livelock row and 0.28 hang), fcsel0 s24 (0.37), fcsel3m s2 (0.37); explain.py with trigger chains and shift-paired arrivals; supersedes c_explain4): the PICOSECOND form of the partial-ack hangs at ulink_n_falseResult_7 stage 0's controller (fcsel1 s24 at 0.09, item 28 at 0.36), and fcsel1 s24's finite race (PROGRAM 7acb3a72): run.sh restricted (ONLY=) to the race
# already reported (with the build SDF: slack at nominal SDF), then tools/margin/explain.py (capture, split, both paths cells/routing, slack, x 8.5 % error), names from the routed JSON.
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
CP="K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; KN=\"$COL\"; KER=collatz; PAIRS=\"27,27 703,703 77031,77031\""
case $TASK in
1) NAME=item27_xorshift_s2; K=xorshift; MLIR=research/data/fifteen/xorshift_predec.mlir; KN="$XOR BDC_FORK_OUT_LINK=n11__0"; SZ=research/data/xorshift_sizes_T3s50_fr4_bench.vh; SEED=2; KER=xorshift; PAIRS="0x92d68ca2,3 0x92d68ca2,4 0x92d68ca2,8 0x92d68ca2,5"; KEYS="SLICE_X15Y33.B6:102 SLICE_X14Y30.B6:102";;
2) NAME=fcsel0_s24; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s0_bench.vh; SEED=24; KEYS="SLICE_X18Y23.B6:102";;
3) NAME=fcsel3m_s2; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh; SEED=2; KEYS="SLICE_X18Y26.A6:101 SLICE_X18Y28.A6:102";;
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
W=$RUNS/m; mkdir -p $W; echo $KEYS | tr ' ' '\n' > $RUNS/only.txt
MINIMIZE=1 HOSTDELAY=2000 SDF=$B/${K}_bench_gen.sdf ONLY=$RUNS/only.txt CONES=1 STEER=1 SIM=simx KERNEL=$KER PAIRS="$PAIRS" TFULL=25000000 LATCH=1 W0=1 KLO=0.0 JOBS=${JOBS:-8} \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
rc=$?
for f in names.txt arbs.json kappa_hi.txt checked.txt margins.txt summary.txt md5.txt run.log bnd.json; do [ -f $W/$f ] && cp $W/$f $OUT/; done
cp $W/explain_*.txt $OUT/ 2>/dev/null; [ -d $W/witness ] && { mkdir -p $OUT/witness; cp $W/witness/*.txt $W/witness/*.json $OUT/witness/ 2>/dev/null; }
exit $rc
