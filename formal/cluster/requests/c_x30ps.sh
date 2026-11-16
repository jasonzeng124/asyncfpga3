#!/bin/bash
#CLUSTER array=1 cores=8 mem=32G time=90
# Shard C: item 30's entry-steer split (FOR-RESEARCH C21) in picoseconds: the flips at every input pin of ucond_br2/3/4
# around the n = 97 offer in draw 5 (failing) and with a 1-ps host (passing); research's rule E rows (skew.py -v, unchanged)
# for the entry steers on this route; and the band thresholds (CARRY band, chain band) by bisection on draw 5.
set -uo pipefail
R=$PEER
COL="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
K=collatz64; MLIR=research/data/fifteen/collatz64_preeq2.mlir; SZ=research/data/collatz64_sizes_T4cdb_h4s3_bench.vh; SEED=10
mkdir -p $R/build/frontend; [ -d $R/build/frontend/$K ] || cp -r $R/cloud/fixtures/frontend/* $R/build/frontend/
cp $R/$MLIR $R/build/frontend/$K/comp/handshake_transformed.mlir
source "$TC/openxc7/export.sh" > /dev/null
( cd $R/cells && env $COL NEXTPNR_SEED=$SEED BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$R/$SZ ./hw/build_bench.sh $K ) > $RUNS/build.log 2>&1
B=$R/cells/build/hw/${K}_bench_gen; md5sum $B/${K}_bench_gen.sdf > $OUT/build.txt
( cd $R/cells/verify && python3 skew.py -v $B/${K}_bench_gen.sdf ) > $RUNS/skew.txt 2>&1
grep -A9 -E "^  (VIOLATED|SLACK   |ok      ) bd_steer .*ucond_br[234]$" $RUNS/skew.txt > $OUT/rule_e_entry_steers.txt
W=$RUNS/m; mkdir -p $W
DRAWS=1 DRAW_SEED0=5 DRAW_MODEL=research HOSTDELAY=12000 SIM=simx KERNEL=$K PAIRS="27,27 1,1 97,97" TFULL=25000000 LATCH=1 \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json KV=$R/cells/build/gen/${K}_kernel_bench.v \
  BV=$R/cells/build/gen/${K}_bench_gen.v bash formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $W > $OUT/run.txt 2>&1
X="$W/simx $W/net.simx --periodic --maxev 100000000 --kernel collatz64 --corner 0 --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq --tmax 7000000 --draw 5 --gclass $W/gclass.txt --sreg 0.02 --sarc 0.126 --want 111,0,118 --pairs 27,27 1,1 97,97 --w 20"
$X --bands 0.216531,0.225189,0.986890 --hostdelay 12000 --dump $RUNS/fail.json > /dev/null 2>&1
$X --bands 0.216531,0.225189,0.986890 --hostdelay 1 --dump $RUNS/pass.json > /dev/null 2>&1
python3 - $W/net.json $W/routed.json $RUNS/fail.json $RUNS/pass.json > $OUT/steer_pins.txt 2>&1 <<'PY'
import json, re, sys
N = json.load(open(sys.argv[1])); names = N["nodes"]; G = N["gates"]
cells = json.load(open(sys.argv[2]))["modules"]["top"]["cells"]
bel = {c["attributes"].get("NEXTPNR_BEL"): n for n, c in cells.items() if c.get("attributes", {}).get("NEXTPNR_BEL")}
drv = {g["out"]: g for g in G}
def cn(g):
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"]); return bel.get("%s/%s%sLUT" % m.groups(), "") if m else ""
def src(n, depth=0):   # walk back through pips/hops to the driving LUT / cell
    g = drv.get(n)
    while g and g["kind"] in ("pip", "hop") and depth < 200: n = g["ins"][0]; g = drv.get(n); depth += 1
    return (cn(g) or (g["name"] if g else names[n])) if g else names[n]
for tag, f in (("FAIL (draw 5, host 12 ns)", sys.argv[3]), ("PASS (draw 5, host 1 ps)", sys.argv[4])):
    D = json.load(open(f))["nodes"]
    print("==", tag)
    for g in G:
        if g["kind"] in ("lut6", "lut5") and re.search(r"ucond_br[234]\.u\$LUT6", cn(g)):
            print(" ", cn(g), g["name"], "out flips 3.50-3.56 us:", [t for t in D.get(str(g["out"]), [0, []])[1] if 3500000 <= t <= 3560000])
            for i, (n, arc) in enumerate(zip(g["ins"], g["arcs"])):
                h = [t for t in D.get(str(n), [0, []])[1] if 3500000 <= t <= 3560000]
                print("    pin %d  from %-60s  arc fast [%d,%d] slow [%d,%d]  flips %s" % (i, src(n)[:60], arc["fmin"], arc["fmax"], arc["smin"], arc["smax"], h))
PY
echo "== bisection on draw 5 (host 12 ns): CARRY4/F7/F8 band b_cells (fails at 0.50, passes at 0.40)" > $OUT/thresholds.txt
lo=0.40; hi=0.50
for i in 1 2 3 4 5 6; do m=$(python3 -c "print(round(($lo+$hi)/2,5))"); r=$($X --bands 0.216531,0.225189,$m --hostdelay 12000 2>&1 | grep -c "RESULT OK")
  echo "b_cells $m: $([ $r = 1 ] && echo PASS || echo FAIL)" >> $OUT/thresholds.txt; [ $r = 1 ] && lo=$m || hi=$m; done
echo "== chain band b_c (fails at 0.2165, passes at 0.27), b_cells 0.98689" >> $OUT/thresholds.txt
lo=0.216531; hi=0.27
for i in 1 2 3 4 5 6; do m=$(python3 -c "print(round(($lo+$hi)/2,5))"); r=$($X --bands $m,0.225189,0.986890 --hostdelay 12000 2>&1 | grep -c "RESULT OK")
  echo "b_c $m: $([ $r = 1 ] && echo PASS || echo FAIL)" >> $OUT/thresholds.txt; [ $r = 1 ] && hi=$m || lo=$m; done
echo "== host delay (fails at 12 ns, passes at 1 ps)" >> $OUT/thresholds.txt
for h in 100 500 1000 2000 4000 8000 16000 50000; do r=$($X --bands 0.216531,0.225189,0.986890 --hostdelay $h 2>&1 | grep -c "RESULT OK"); echo "host $h ps: $([ $r = 1 ] && echo PASS || echo FAIL)" >> $OUT/thresholds.txt; done
exit 0
