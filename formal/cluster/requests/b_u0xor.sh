#!/bin/bash
#CLUSTER array=1-24 cores=2 mem=16G time=150
# Shard B (b_u0xor): xorshift x55a10 (research's current candidate: item 35 + UCMPI0 10) with UADDI0 kept (12, odd tasks)
# vs UADDI0 0 (even tasks), seeds 1-12 (task 2s-1 / 2s). Per route: xor19 draws K 2101-2104 (research's model), the loop
# counter preloaded at 0x3ffffff0 (tools-B/preload, FOR-RESEARCH B2) 8 draws, per-iteration period of a 271-iteration
# preloaded call (2 draws), and C's steermargin for ucmpi1 (loop test) and ucmpi0 (entry) at chains 0.20 / rest 0.31 /
# CARRY 1.0, xor19 + xorlong. Untrusted simulation.
set -uo pipefail
R=$PEER
SEED=$(( (TASK + 1) / 2 )); V=$(( TASK % 2 ))   # V 1 = keep UADDI0 12, 0 = UADDI0 0
K=xorshift; SZ0=$R/research/data/xorshift_sizes_T3s50_fr4a_x55a10_bench.vh; SZ=$RUNS/sizes.vh
if [ $V = 1 ]; then cp $SZ0 $SZ; else sed 's/^`define BD_SZ_BRIDGE_I_UDUT_UADDI0 .*/`define BD_SZ_BRIDGE_I_UDUT_UADDI0 0/' $SZ0 > $SZ; fi
grep UADDI0 $SZ > $OUT/sizes_uaddi0.txt
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
mkdir -p $R/build/frontend/$K/comp; cp $R/research/data/fifteen/xorshift_predec.mlir $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 \
  BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 \
  BD_SIZES=$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
B=$R/cells/build/hw/${K}_bench_gen; echo "seed $SEED uaddi0 $([ $V = 1 ] && echo 12 || echo 0)" > $OUT/build.txt
md5sum $B/${K}_bench_gen.sdf >> $OUT/build.txt; python3 $R/research/tools/ffmux_scan.py $B/${K}_bench_gen.fasm > /dev/null 2>&1; echo "ffmux $?" >> $OUT/build.txt
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' $R/research/data/eventgraph/gate/xor19.hex)
W=$RUNS/m; mkdir -p $W
JOBS=2 DRAWS=4 DRAW_SEED0=2101 DRAW_MODEL=research HOSTDELAY=12000 KERNEL=$K PAIRS="$PAIRS" TFULL=40000000 \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
cp $W/draws_summary.txt $OUT/
P3="0x92d68ca2,0x3 0x9e3779b9,0x3 0x12345678,0x64"; W3=$(python3 formal/tools/margin/kernels.py xorshift $P3)
$W/simx $W/net.simx --want $W3 --hostdelay 12000 --pairs $P3 --kernel xorshift --corner 0 --data0 --full --R 400000 --su 1000 \
  --datachange broad --nextreq seq --tmax 40000000 --draw 2101 --gclass $W/gclass.txt --bands 0.25,0.25,0.6 --sreg 0.02 --w 20 --dump $W/ref_dump.json > /dev/null 2>&1
PA="0x92d68ca2,0x3ffffff1 0x92d68ca2,0x3fffffff 0x92d68ca2,0x40000000 0x92d68ca2,0x40000001 0x13579bdf,0x40000001 0xdeadbeef,0x40000010 0x9e3779b9,0x40000002"
TMPDIR=$RUNS formal/tools-B/preload/prun.sh $W $RUNS/pa 0x3ffffff0 ulink_n6 "$PA" 8 2101 2 > $OUT/preloadA.txt 2>&1
gcc -O2 -o $RUNS/oracle formal/tools-B/preload/oracle.c
python3 formal/tools-B/preload/preload_net.py $W/net.json $W/routed.json $RUNS/per.json --link ulink_n6 --value 0x3ffffff0 2>/dev/null
python3 formal/tools/margin/simx_conv.py $RUNS/per.json $W/bnd.json $RUNS/per.simx > /dev/null 2>&1
PP="0x92d68ca2,0x40000100"; WP=$($RUNS/oracle xorshift 0x3ffffff0 $PP)
for KK in 2101 2102; do BB=$(python3 -c "import random; r=random.Random(7919*$KK+17); print('%.6f,%.6f,%.6f'%(r.uniform(.2,.31),r.uniform(.2,.31),r.uniform(.2,1.0)))")
  $W/simx $RUNS/per.simx --want $WP --hostdelay 12000 --pairs $PP --kernel xorshift --corner 0 --data0 --full --R 400000 --su 1000 \
    --datachange broad --nextreq seq --tmax 40000000 --draw $KK --gclass $W/gclass.txt --bands $BB --sreg 0.02 --sarc 0.126 --w 20 \
    --dump $RUNS/pd.json 2>&1 | grep -o "RESULT [A-Z]*" >> $OUT/period.txt
  python3 formal/tools-B/preload/period.py $RUNS/per.json $W/routed.json $RUNS/pd.json 'udut\.umux0\.uor$' | sed "s/^/K$KK /" >> $OUT/period.txt; done
XL=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' formal/tools/margin/vec/xorlong.hex)
for c in 'ucmpi1\..*uz_n41' 'ucmpi0\..*uz_n3$'; do
  python3 formal/tools/margin/steermargin.py $W "$c" --kernel xorshift --pairs $PAIRS $XL --bands 0.20,0.31,1.0 > $RUNS/sm.txt 2>&1
  echo "### $c" >> $OUT/steer.txt; cut -c1-260 $RUNS/sm.txt >> $OUT/steer.txt; done
exit 0
