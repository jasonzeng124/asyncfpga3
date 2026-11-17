#!/usr/bin/env bash
# suite_one.sh KERNEL SEED [NDRAWS] [MAXIT] -- one kernel of the compiler suite through the automatic path, one placer
# seed (PROGRAM "A benchmark suite for the compiler", owner 2026-11-17).  Nothing here is set for a kernel by name except
# where its verification data lives (vectors, oracle), which is per kernel by nature.
#   1. research/tools/auto/auto_size.sh: BDC_AUTO=1, sizes from the one rule (corner_audit CA_SIZERULE=1) on the route
#      as built, re-route and ratchet until the rule is clean on its own route or MAXIT routes were built.  The static
#      rule is a tool here, not a gate (PROGRAM "The board decides"): a NOT CLEAN loop still goes to the draws.
#   2. the bits: fasm_equiv EQUIVALENT and ffmux_scan clean, else the route is not a board route (reported, not judged).
#   3. NDRAWS draws of the delay model (bench_gate.sh draw:K, K = 10000 + 100 * SEED + j: a different model point on
#      every route), the kernel's vectors, expected values compiled from the C at run time (never recorded from a run).
#   4. metrics: P (timed event graph on the period vector), latency per call (BENCHRES, host cycles of 12 ns), kernel
#      LUTs (SLICE_LUTX cells under the DUT in the routed JSON).
# Writes $RUNS/suite/KERNEL_SEED/{result.txt, draws.txt, exp.txt}; prints the result line.
set -uo pipefail
K=$1; S=$2; ND=${3:-4}; MAXIT=${4:-4}
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/home/user/runs}; export RUNS
O=$RUNS/suite/${K}_$S; mkdir -p "$O"; : > "$O/draws.txt"
D=${K}_bench_gen
# verification data: the six original kernels use their gate vectors and oracles (with the bench's input masks);
# every other kernel reads kernels/K/vec.hex and the generic oracle research/tools/suite/oracle.sh
case $K in
  xorshift) V=research/data/eventgraph/gate/xor19.hex; PV=research/data/fifteen/vec_xorshift.hex; OR="research/tools/fifteen/kernel_oracle.sh xorshift";;
  collatz) V=research/data/eventgraph/gate/col18.hex; PV=research/data/fifteen/vec_collatz.hex; OR="research/tools/fifteen/kernel_oracle.sh collatz";;
  collatz64) V=research/data/eventgraph/gate/c6419.hex; PV=research/data/fifteen/vec_c64_871.hex; OR="research/tools/fifteen/kernel_oracle.sh collatz64";;
  ipow) V=research/data/eventgraph/gate/ipow17.hex; PV=research/data/fifteen/vec_ipow.hex; OR="research/tools/fifteen/kernel_oracle.sh ipow";;
  isprime) V=research/data/alltable/isp17.hex; PV=research/data/alltable/vec_isprime_cost.hex; OR="research/tools/fifteen/kernel_oracle.sh isprime";;
  gcd) V=research/data/eventgraph/gate/gcd18.hex; PV=research/data/aug_gcd/gcdcost_vec.hex; OR="research/data/gcd_draws/gcd_oracle.sh";;
  *) V=kernels/$K/vec.hex; PV=kernels/$K/period.hex; [ -f "$R/$PV" ] || PV=$V; OR="research/tools/suite/oracle.sh $K";;
esac
fin() { echo "$K $S $*" | tee "$O/result.txt"; exit 0; }
[ -f "$R/$V" ] || fin "status=NO-VECTORS ($V)"
( cd "$R" && $OR < "$V" ) > "$O/exp.txt" 2> "$O/oracle.err" || fin "status=NO-ORACLE ($(head -1 "$O/oracle.err"))"
[ "$(grep -c . "$O/exp.txt")" = "$(grep -c . "$R/$V")" ] || fin "status=NO-ORACLE (line count)"
N=su_${K}_$S
"$R/research/tools/auto/auto_size.sh" "sl_${K}_$S" "$N" "$K" "$S" "$R/$PV" "$MAXIT" > "$O/auto.log" 2>&1
AR=$(tail -1 "$RUNS/auto/$N/result.txt" 2>/dev/null)
case $AR in
  CLEAN*) IT=$(echo "$AR" | grep -o 'it=[0-9]*' | cut -d= -f2); RULE=clean;;
  "NOT CLEAN after"*) IT=$(echo "$AR" | sed -n "s/^NOT CLEAN after \([0-9]*\).*/\1/p"); RULE=not-clean;;
  "NOT CLEAN it="*) IT=$(echo "$AR" | grep -o 'it=[0-9]*' | cut -d= -f2); RULE=not-clean-unfixable;;
  "BUILD FAILED it=0"*) fin "status=DOES-NOT-COMPILE ($(grep -m1 -i 'error' "$RUNS/hw/${N}_0/build.log" | cut -c1-160))";;
  *) fin "status=FLOW-FAILED ($AR)";;
esac
RT=${N}_$IT; HW=$RUNS/hw/$RT; RD=$RUNS/r/$RT
LINE=$(cat "$RUNS/auto/$N/it_$IT.txt" 2>/dev/null)
md5=$(echo "$LINE" | awk '{print $2}'); P=$(echo "$LINE" | grep -o 'P=[0-9A-Z]*' | cut -d= -f2)
eq=$(echo "$LINE" | grep -q 'NOT EQUIVALENT' && echo NOT-EQUIVALENT || (echo "$LINE" | grep -q 'EQUIVALENT' && echo EQUIVALENT || echo EQUIV?))
ff=$(echo "$LINE" | grep -q 'FFMUX-FLAG' && echo FFMUX-FLAG || echo ffmux-clean)
luts=$(python3 - "$HW/${D}_routed.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))["modules"]
n = sum(1 for t in m.values() for c, v in t.get("cells", {}).items() if v["type"] == "SLICE_LUTX" and "udut" in c)
print(n)
PY
)
lat=$(grep BENCHRES "$RD/run.log" 2>/dev/null | grep -o 'latmax=[0-9]*' | cut -d= -f2 | sort -n | tail -1)
base="P=${P:-NA} lat_max_cyc=${lat:-NA} luts=$luts sdf=$md5 rule=$RULE it=$IT bits=$eq $ff"
if [ "$eq" != EQUIVALENT ] || [ "$ff" != ffmux-clean ]; then fin "status=NOT-A-BOARD-ROUTE $base"; fi
# DRAW_JOBS draws at a time (default 1); each draw has its own work directory and draw file
draw() { local k=$1 g
  g=$("$R/research/tools/eventgraph/bench_gate.sh" "$HW" "$D" "$RUNS/g/$RT/d$k" "$R/$V" "$O/exp.txt" "draw:$k" 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3-8 "$RUNS/g/$RT/d$k/draw_$k.txt" 2>/dev/null) :: ${g:-none}" > "$O/draw_$k.txt"
  rm -rf "$RUNS/g/$RT/d$k/draw_$k" 2>/dev/null; }
mkdir -p "$RUNS/g/$RT"; [ -f "$RD/xray.sdf" ] && for j in $(seq 1 "$ND"); do k=$((10000 + 100 * S + j)); mkdir -p "$RUNS/g/$RT/d$k"; cp "$RD/xray.sdf" "$RUNS/g/$RT/d$k/xray.sdf"; done
for j in $(seq 1 "$ND"); do
  draw $((10000 + 100 * S + j)) &
  while [ "$(jobs -rp | wc -l)" -ge "${DRAW_JOBS:-1}" ]; do sleep 5; done
done; wait
pass=0
for j in $(seq 1 "$ND"); do k=$((10000 + 100 * S + j)); cat "$O/draw_$k.txt" >> "$O/draws.txt"; grep -q ":: PASS " "$O/draw_$k.txt" && pass=$((pass + 1)); done
st=PASS; [ "$pass" = "$ND" ] || st=FAIL
fin "status=$st draws=$pass/$ND $base"
