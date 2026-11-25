#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=16G time=60
# Shard C: the controller-feedback race of FOR-RESEARCH C13 over routes (static, fbslack.py on the build's SDF; no simulation):
# tasks 1-16 = item 28's structure (fcsel3m, nl6s3m) seeds 1-16, tasks 17-32 = item 27's structure (xorshift pre_dec fr4) seeds 1-16.
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
CP="K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; KN=\"$COL\"; KER=collatz; PAIRS=\"27,27 703,703 77031,77031\""
if [ $TASK -le 16 ]; then SEED=$TASK; NAME=fcsel3m_s$SEED; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh
else SEED=$((TASK-16)); NAME=x27_s$SEED; K=xorshift; MLIR=research/data/fifteen/xorshift_predec.mlir; KN="$XOR BDC_FORK_OUT_LINK=n11__0"; SZ=research/data/xorshift_sizes_T3s50_fr4_bench.vh; KER=xorshift; fi
case $TASK in *) ;;
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
python3 formal/tools/margin/fbslack.py $B/${K}_bench_gen.sdf --top 400 --grep .ctl. > $OUT/fbslack_ctl.txt 2>&1
python3 formal/tools/margin/fbslack.py $B/${K}_bench_gen.sdf --top 40 > $OUT/fbslack.txt 2>&1
rc=0
exit $rc
