#!/bin/bash
#CLUSTER array=1 cores=8 mem=32G time=60
# Shard C: c_x30dbg follow-up: item 30 draw 5 (27, 1, 97) emits a SECOND 0 for n = 1, 22 ns after the first; the
# LUT nodes whose flip count differs between it and its passing variants (chain band 0.27; host 1 ps), with names.
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
K=collatz64; MLIR=research/data/fifteen/collatz64_preeq2.mlir; SZ=research/data/collatz64_sizes_T4cdb_h4s3_bench.vh; SEED=10
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $COL NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
B=$R/cells/build/hw/${K}_bench_gen; md5sum $B/${K}_bench_gen.sdf > $OUT/build.txt
W=$RUNS/m; mkdir -p $W
DRAWS=1 DRAW_SEED0=5 DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="27,27 1,1 97,97" TFULL=25000000 LATCH=1 \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
X="$W/simx $W/net.simx --periodic --maxev 100000000 --kernel collatz64 --corner 0 --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq --tmax 7000000 --draw 5 --gclass $W/gclass.txt --sreg 0.02 --sarc 0.126 --want 111,0,118 --pairs 27,27 1,1 97,97 --w 20"
$X --bands 0.216531,0.225189,0.986890 --hostdelay 12000 --dump $RUNS/fail.json > $OUT/fail.txt 2>&1
$X --bands 0.27,0.225189,0.986890 --hostdelay 12000 --dump $RUNS/chain.json > $OUT/chain.txt 2>&1
$X --bands 0.216531,0.225189,0.986890 --hostdelay 1 --dump $RUNS/host1.json > $OUT/host1.txt 2>&1
$X --bands 0.216531,0.225189,0.40 --hostdelay 12000 --dump $RUNS/cells.json > $OUT/cells.txt 2>&1
for v in chain host1 cells; do
  python3 formal/tools/margin/diverge.py $W/net.json $RUNS/fail.json $RUNS/$v.json --routed $W/routed.json --top 40 > $OUT/diverge_$v.txt 2>&1
done
# the boundary nodes' flips in the failing run between 3.40 and 3.60 us (names)
python3 - $W/net.json $W/bnd.json $RUNS/fail.json > $OUT/boundary_fail.txt 2>&1 <<'PY'
import json, sys
N = json.load(open(sys.argv[1]))["nodes"]; B = json.load(open(sys.argv[2]))["boundary"]; D = json.load(open(sys.argv[3]))["nodes"]
idx = {n: i for i, n in enumerate(N)}
for k in ("req", "a_ack", "b_ack", "start_ack", "out0_req", "out0_ack", "pend_ack"):
    h = D.get(str(idx[B[k]]), [False, []])[1]
    print(k, B[k], [t for t in h if 3300000 <= t <= 3600000])
PY
exit 0
