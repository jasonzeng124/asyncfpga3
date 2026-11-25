#!/bin/bash
#CLUSTER array=1-3 cores=16 mem=64G time=120
# Shard C: research's draws1 control (c7) in formal's simx: item 27 fxd s2, ucond_br6's CONDITION arcs (the inputs of
# ucond_br6.u$LUT6/LUT5 not driven by ucond_br6_j, as research's sdf_inject regex) +3000 ps on draws 1-16 (task 1) and
# +8000 ps on draws 17-32 (task 2); task 3 no injection, draws 1-32. Research's model, fixed host. Research: "the draw
# model must fail the +8000 half".
set -uo pipefail
R=$PEER
XOR="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0"
K=xorshift; MLIR=research/data/fifteen/xorshift_predec.mlir; SZ=research/data/xorshift_sizes_T3s50_fr4_bench.vh; SEED=2
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $XOR BDC_FORK_OUT_LINK=n11__0 NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
B=$R/cells/build/hw/${K}_bench_gen; md5sum $B/${K}_bench_gen.sdf > $OUT/build.txt
W=$RUNS/m; mkdir -p $W
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' $R/research/data/eventgraph/gate/xor19.hex)
COMMON="DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K TFULL=400000000 LATCH=1 JOBS=16 SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v BV=$R/cells/build/gen/${K}_bench_gen.v"
# decode once (DRAWS=1), then build the injection list
env $COMMON DRAWS=1 PAIRS="$PAIRS" bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/decode.txt 2>&1
case $TASK in 1) PS=3000; S0=1; ND=16;; 2) PS=8000; S0=17; ND=16;; 3) PS=0; S0=1; ND=32;; esac
python3 - $W/net.json $W/routed.json $PS $RUNS/inj.json > $OUT/inject.txt 2>&1 <<'PY'
import json, re, sys
N = json.load(open(sys.argv[1])); G = N["gates"]; names = N["nodes"]; ps = int(sys.argv[3])
cells = json.load(open(sys.argv[2]))["modules"]["top"]["cells"]
bel = {c["attributes"].get("NEXTPNR_BEL"): n for n, c in cells.items() if c.get("attributes", {}).get("NEXTPNR_BEL")}
drv = {g["out"]: g for g in G}
def cn(g):
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"]); return bel.get("%s/%s%sLUT" % m.groups(), "") if m else ""
def src(n):
    g = drv.get(n); d = 0
    while g and g["kind"] in ("pip", "hop") and d < 300: n = g["ins"][0]; g = drv.get(n); d += 1
    return (cn(g) or g["name"]) if g else names[n]
inj = []
for g in G:
    if g["kind"] in ("lut6", "lut5") and re.search(r"\.ucond_br6\.u\$LUT[56]$", cn(g)):
        for p, u in enumerate(g["ins"]):
            s = src(u)
            if "_j.u" in s or "GND" in s or "VCC" in s: continue
            inj.append([names[g["out"]], p, ps]); print("inject +%d on %s (%s) pin %d from %s" % (ps, names[g["out"]], cn(g), p, s))
json.dump({"S": [], "F": [], "I": inj if ps else []}, open(sys.argv[4], "w"))
PY
rm -f $W/draws.txt $W/draws_summary.txt
env $COMMON DRAWS=$ND DRAW_SEED0=$S0 DRAW_INJECT=$RUNS/inj.json PAIRS="$PAIRS" bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
cp $W/draws.txt $W/draws_summary.txt $OUT/ 2>/dev/null
exit 0
