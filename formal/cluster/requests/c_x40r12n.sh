#!/bin/bash
#CLUSTER array=1 cores=8 mem=32G time=90
# Shard C (c_x40r12n: c_x40r12 with routed names on every RACES / NEARMISS node, all 5 closest rows, and the uniform corners). (c_x40r12:) route 12 of collatz x0.40 failed every in-model variant in c_x40col2; here bands OUTSIDE the model (chains up to 1.0, rest down to 0.05) and RACES=1 (copy-chain fix), to see whether a slower chain clears it and which LUT races. (from c_x40col2:)
# (0/32: [111, 0, 0] or no answer), task 2 route 20 (draw 1 answers 106 for n = 27; draw 3 passes), task 3 route 7
# (stops after 3 answers). Draw 1 (research's model) as drawn, each band class moved, no pip scatter; then the LUTs whose
# flip count differs from the first passing variant (diverge.py, routed names). col14, fixed host 12 ns.
set -uo pipefail
R=$PEER
SS=(12 20 7); SEED=${SS[$((TASK-1))]}; F=40
K=collatz; MLIR=research/data/fifteen/collatz_preeq2.mlir; SZ=research/data/collatz_sizes_T3cdb_nl6s3a_fx${F}_bench.vh
python3 $R/research/tools/shrink_sizes.py $R/research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh 0.$F $R/$SZ > $OUT/shrink.txt 2>&1
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $COL NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
B=$R/cells/build/hw/${K}_bench_gen; echo "x0.$F route $SEED" > $OUT/build.txt; md5sum $B/${K}_bench_gen.sdf $B/${K}_bench_gen.fasm >> $OUT/build.txt
cp $R/$SZ $OUT/sizes.vh
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $1}' $R/research/data/eventgraph/gate/col14.hex)
W=$RUNS/m; mkdir -p $W
DRAWS=4 DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="$PAIRS" TFULL=400000000 LATCH=1 \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
cp $W/draws.txt $OUT/
WANT=$(python3 formal/tools/margin/kernels.py collatz $PAIRS)
X="env RACES=1 $W/simx $W/net.simx --periodic --maxev 1000000000 --kernel collatz --want $WANT --pairs $PAIRS --corner 0 --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq --tmax 400000000 --hostdelay 12000 --draw 1 --gclass $W/gclass.txt --sreg 0.02 --sarc 0.126 --w 20"
v() { L=$1; shift; echo "=== $L | $*" >> $OUT/runs.txt; $X "$@" --dump $RUNS/$L.json > $RUNS/$L.out 2>&1; grep -E "^RESULT|MAXEV|^RACES|^NEARMISS" $RUNS/$L.out | sed 's/want \[[^]]*\]//' | cut -c1-250 >> $OUT/runs.txt; grep "^out0" $RUNS/$L.out | head -6 >> $OUT/runs.txt; }
v asis --bands 0.269827,0.261244,0.765207
v slowall --bands 1.0,1.0,1.0
v fastall --bands 0.0,0.0,0.0
v mid --bands 0.5,0.5,0.5
for L in asis slowall fastall mid; do grep -E "^RACES|^NEARMISS|^out0|^RESULT" $RUNS/$L.out | python3 formal/tools/margin/namelines.py $W/routed.json > $OUT/named_$L.txt; done
python3 - $W/net.json $W/routed.json > $OUT/sources.txt <<'PY'
# for the closest storage-race LUTs: each pin's driving LUT through copy chains, named
import json, sys, re
sys.path.insert(0, "formal/tools/margin"); import namelines
N = json.load(open(sys.argv[1])); G = N["gates"]; names = N["nodes"]; bel = namelines.belmap(sys.argv[2])
drv = {g["out"]: g for g in G}; idx = {n: i for i, n in enumerate(names)}
def src(u):
    for _ in range(200):
        g = drv.get(u)
        if g is None or g["k"] != 1 or g["init"] != 2 or re.search(r"LUT|\.[A-D][56]$", g["name"]): break
        u = g["ins"][0]
    return names[u]
for nd in ["SLICE_X22Y33.A6", "SLICE_X22Y36.B5", "SLICE_X24Y37.B5", "SLICE_X18Y30.D6", "SLICE_X20Y42.C5", "SLICE_X22Y42.D5"]:
    g = drv.get(idx.get(nd, -1))
    if not g: print(nd, "not found"); continue
    print(namelines.name(bel, nd), "INIT %x" % g["init"], " ".join("p%d<-%s" % (p, namelines.name(bel, src(u))) for p, u in enumerate(g["ins"])))
PY
exit 0
