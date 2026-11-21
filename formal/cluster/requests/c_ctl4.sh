#!/bin/bash
#CLUSTER array=1 cores=16 mem=64G time=120
# Shard C (c_ctl4 = c_ctl3 redone: a run counts as FAIL only on RESULT MISMATCH; a run with no verdict (crash, memory) is
# retried and reported; 8 at a time). Was c_ctl3: formal's threshold injection (ps, 50-ps resolution) on ucond_br6's condition for each draw 1-32 of
# research's model on item 27 fxd s2 -- formal's slack of that steer race per draw, to set beside research's. (c_ctl2 traced the one disagreement of c_ctl1 (+3000, draw 15 hangs in formal, passes in research): runt filter
# width, injection size, the stall (stderr), and diverge.py against a passing variant. Was c_ctl1: research's draws1 control (c7) in formal's simx: item 27 fxd s2, ucond_br6's CONDITION arcs (the inputs of
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
PS=3000
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
for ps in 2000 2500 3000 3500; do python3 -c "import json,sys; d=json.load(open('$RUNS/inj.json')); [x.__setitem__(2,$ps) for x in d['I']]; json.dump(d,open('$RUNS/inj_$ps.json','w'))"; done
WANT=$(python3 formal/tools/margin/kernels.py xorshift $PAIRS)
th() { K=$1; B=$(python3 -c "import random; r=random.Random(7919*$K+17); print('%.6f,%.6f,%.6f' % (r.uniform(.2,.31), r.uniform(.2,.31), r.uniform(.2,1.0)))")
  lo=0; hi=8000
  for i in $(seq 1 8); do m=$(( (lo+hi)/2 )); python3 -c "import json; d=json.load(open('$RUNS/inj.json')); [x.__setitem__(2,$m) for x in d['I']]; json.dump(d,open('$RUNS/i_$K.json','w'))"
    for try in 1 2 3; do
      r=$($W/simx $W/net.simx --periodic --maxev 1000000000 --kernel xorshift --want $WANT --pairs $PAIRS --corner 0 --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq --tmax 400000000 --hostdelay 12000 --draw $K --gclass $W/gclass.txt --bands $B --sreg 0.02 --sarc 0.126 --classes $RUNS/i_$K.json --w 20 2>&1 | grep -oE "RESULT (OK|MISMATCH)" | head -1)
      [ -n "$r" ] && break; echo "draw $K +$m: no verdict (try $try)" >&2; done
    if [ "$r" = "RESULT OK" ]; then lo=$m; elif [ "$r" = "RESULT MISMATCH" ]; then hi=$m; else echo "draw $K: UNDECIDED at +$m"; break; fi; done
  echo "draw $K bands $B: passes at +$lo ps, fails at +$hi ps"; }
for K in $(seq 1 32); do th $K & [ $((K % 8)) = 0 ] && wait; done > $OUT/thresholds.txt 2> $OUT/noverdict.txt; wait
sort -n -k2 $OUT/thresholds.txt -o $OUT/thresholds.txt
exit 0
