#!/bin/bash
#CLUSTER array=1-17 cores=16 mem=64G time=240
# Shard C: the BOARD APPROXIMATOR (PROGRAM "The board decides", 2026-11-16): per route, 64 random delay draws of the
# circuit decoded from the bitstream (draws.py / simx --draw: band 0.38, region 0.16 on 10x10 slices, arc 0.126,
# lognormal = research's fid model), H_RUNT(20), host 12 ns, research's own gate vectors (col15 / c6416 / xor19);
# the fraction of draws returning the right answers. No adversary. Board candidates on their board seeds, the two
# known-bad builds and nc64_7's good neighbour, and 3 more routes of items 33 and 32.
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
XP="K=xorshift; MLIR=research/data/fifteen/xorshift_predec.mlir; KN=\"$XOR BDC_FORK_OUT_LINK=n11__0\"; V=xor19"
CP="K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; KN=\"$COL\"; V=col15"
C64="K=collatz64; MLIR=research/data/fifteen/collatz64_preeq2.mlir; KN=\"$COL\"; V=c6416"
case $TASK in
1) NAME=item27_s2; eval "$XP"; SZ=research/data/xorshift_sizes_T3s50_fr4_bench.vh; SEED=2;;
2) NAME=item33_s27; eval "$XP"; SZ=research/data/xorshift_sizes_T3s50_fr4a_bench.vh; SEED=27;;
3) NAME=item28_s20; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh; SEED=20;;
4) NAME=item31_s20; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh; SEED=20;;
5) NAME=item25_s24; eval "$CP"; SZ=research/data/collatz_sizes_T3cdb_nl4_bench.vh; SEED=24;;
6) NAME=item26_s25; eval "$C64"; SZ=research/data/collatz64_sizes_T4cdb_h2_bench.vh; SEED=25;;
7) NAME=item30_s10; eval "$C64"; SZ=research/data/collatz64_sizes_T4cdb_h4s3_bench.vh; SEED=10;;
8) NAME=item32_s22; eval "$C64"; SZ=research/data/collatz64_sizes_T4cdb_h4s3p_bench.vh; SEED=22;;
9) NAME=BAD_xf2_1; K=xorshift; MLIR=; KN="$XOR BDC_FORK_OUT_LINK=n11__0"; V=xor19; SZ=research/data/xorshift_sizes_T3s50_fr2_bench.vh; SEED=1;;
10) NAME=BAD_nc64_7; K=collatz64; MLIR=; KN="BDC_CONST_DATA=1"; V=c6416; SZ=research/data/collatz64_sizes_T4cd_bench.vh; SEED=7;;
11) NAME=pc64_7; K=collatz64; MLIR=; KN="BDC_CONST_DATA=1"; V=c6416; SZ=research/data/fifteen/selectrule/collatz64_sizes_T4cd_sel19_bench.vh; SEED=7;;
12|13|14) SEED=$(echo 1 3 4 | cut -d' ' -f$((TASK-11))); NAME=x33_s$SEED; eval "$XP"; SZ=research/data/xorshift_sizes_T3s50_fr4a_bench.vh;;
15|16|17) SEED=$(echo 1 2 3 | cut -d' ' -f$((TASK-14))); NAME=c64h4s3p_s$SEED; eval "$C64"; SZ=research/data/collatz64_sizes_T4cdb_h4s3p_bench.vh;;
esac
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' $R/research/data/eventgraph/gate/$V.hex)
echo "$NAME K=$K seed=$SEED sizes=$SZ mlir=$MLIR knobs=$KN vectors=$V" > $OUT/build.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/ 2>>$OUT/build.txt
[ -n "$MLIR" ] && cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $KN NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
tail -5 $RUNS/build.log >> $OUT/build.txt
B=$R/cells/build/hw/${K}_bench_gen
md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt 2>&1
W=$RUNS/m; mkdir -p $W
DRAWS=64 HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="$PAIRS" TFULL=400000000 LATCH=1 JOBS=${JOBS:-16} \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
rc=$?
for f in draws.txt draws_summary.txt md5.txt run.log; do [ -f $W/$f ] && cp $W/$f $OUT/; done
exit $rc
