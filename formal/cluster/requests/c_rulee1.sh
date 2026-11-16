#!/bin/bash
#CLUSTER array=1-5 cores=4 mem=16G time=90
# Shard C: research's OWN rule E rows (its cells/verify/skew.py -v, from PEER, on the route's nextpnr SDF + routed JSON)
# for the steer races C19 traced dynamically (item 27 s2 ucond_br9, fcsel3m s2 ucond_br5, fcsel0 s24 merge1 delay,
# item 25 s24 ucond_br6 / the falseResult_3 steer) and for item 33 s27. Ties formal's steer findings to research's slack.
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
CP="K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; KN=\"$COL\""
XP="K=xorshift; MLIR=research/data/fifteen/xorshift_predec.mlir; KN=\"$XOR BDC_FORK_OUT_LINK=n11__0\""
case $TASK in
1) NAME=item27_xorshift_s2; eval "$XP"; SZ=research/data/xorshift_sizes_T3s50_fr4_bench.vh; SEED=2;;
2) NAME=fcsel0_s24; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s0_bench.vh; SEED=24;;
3) NAME=fcsel3m_s2; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh; SEED=2;;
4) NAME=item25_collatz_s24; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl4_bench.vh; SEED=24;;
5) NAME=item33_xorshift_s27; eval "$XP"; SZ=research/data/xorshift_sizes_T3s50_fr4a_bench.vh; SEED=27;;
esac
echo "$NAME K=$K seed=$SEED sizes=$SZ mlir=$MLIR knobs=$KN" > $OUT/build.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/ 2>>$OUT/build.txt
[ -n "$MLIR" ] && cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $KN NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
tail -20 $RUNS/build.log >> $OUT/build.txt
B=$R/cells/build/hw/${K}_bench_gen
md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt 2>&1
ls $B >> $OUT/build.txt
( cd $R/cells/verify && python3 skew.py -v $B/${K}_bench_gen.sdf ) > $OUT/skew_v.txt 2>&1; echo "skew rc=$?" >> $OUT/build.txt
python3 formal/tools/margin/fbslack.py $B/${K}_bench_gen.sdf --top 60 > $OUT/fbslack.txt 2>&1
# the SDF arcs into every steer / merge LUT pin, for a local static walk later
grep -E "INTERCONNECT|IOPATH|INSTANCE" $B/${K}_bench_gen.sdf | xz -9 | base64 > $OUT/sdf_arcs.xz.b64
exit 0
