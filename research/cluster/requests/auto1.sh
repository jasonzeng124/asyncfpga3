#!/bin/bash
#CLUSTER array=1-80 cores=8 mem=32G time=180
# auto1 (PROGRAM "General first", owner 2026-11-17): every kernel with a bench vector set, built with BDC_AUTO=1 and
# NOTHING else -- no instance name, no sizes file, no factor (research/data/auto/README.md). Sizes: "none" = every
# matched delay at bdc/emit.py's own estimate, the sizing of the all-kernel default table (research/data/alltable), so
# the two columns compare like with like. build_bench.sh's MODE=tighten is NOT used: its rule-E converge loop stops
# "NOT CONVERGING" locally on collatz seed 1 at ulink_n14__1 (a link the defaults have too) and on xorshift seed 1 at
# the new rlink / folink select margins (research/data/auto/README.md); sizing is subagent B's. The proven MLIR rewrites are applied by the
# flow itself (bdc/auto.py); MLIR_OVERRIDE below is that same file, only so corner_audit's input.mlir matches the build.
# Tasks: kernel k = (T-1)/16 in xorshift collatz collatz64 ipow gcd, route r = (T-1)%16 + 1. Each: eval_task.sh
# STATIC_ONLY=1 (build + full-stack run + event graph P + static check at nominal / worst), then 2 delay-model draws
# (K = 9000 + 100k + 2r + j; bench_gate.sh draw:K). isprime / fir / single_loop / test_loop_free: no bench vectors or no
# loop / no store support; not here.
# PREDICTION (written before any farm result; local seeds 1-2 in research/data/auto/README.md): event-graph P median,
# as the ratio alltable-default / AUTO at the same "none" sizes: xorshift 1.30 (1.15-1.5), collatz 1.30 (1.1-1.5),
# collatz64 1.25 (1.1-1.4), ipow 1.10 (1.0-1.25), gcd 1.0-1.1 (rule M puts 5 merge pairs of latches on it; the graph
# said storage buys gcd nothing). Draws: 2/2 on every EQUIVALENT ffmux-clean route (the estimates are the long sizes;
# a failure would be a structural bug of the rules or an unsized new select link (olink 4 / rlink 3 / folink 3
# elements), not a short datapath: send it to formal).
set -uo pipefail
KS=(xorshift collatz collatz64 ipow gcd); VS=(xor19 col18 c6415 ipow17 gcd18)
H=0; T=$TASK; Z=none
k=$(( (T-1) / 16 )); S=$(( (T-1) % 16 + 1 )); K=${KS[$k]}; V=${VS[$k]}
G=research/data/eventgraph/gate
case $K in gcd) VEC=research/data/gcd_draws/vec_gcd.hex;; collatz64) VEC=research/data/fifteen/vec_collatz.hex;;
  *) VEC=research/data/fifteen/vec_$K.hex;; esac
mkdir -p build/auto && python3 bdc/auto.py build/frontend/$K/comp/handshake_transformed.mlir build/auto/$K.mlir 2> "$OUT/auto_mlir.txt"
export MLIR_OVERRIDE=build/auto/$K.mlir
NM=au1_${Z}_${K}_$S
echo "auto1 sizes $Z kernel $K seed $S vectors $V" > "$OUT/task.txt"; cat "$OUT/auto_mlir.txt" >> "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $S $VEC $G/$V.hex $G/$V.exp BDC_AUTO=1 > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
cp "$HW/sizes.vh" "$OUT/sizes.vh" 2>/dev/null; cp "$HW/${K}_kernel_bench.v" "$OUT/kernel.v" 2>/dev/null
cp research/data/eventgraph/graphs/$NM/check.txt "$OUT/graph_check.txt" 2>/dev/null
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
md5sum "$HW/$D.sdf" "$RD/xray.sdf" >> "$OUT/task.txt"; head -2 "$OUT/eval.txt" >> "$OUT/task.txt"
run() { j=$1; W=$RUNS/d/$j; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
  r=$(timeout 100m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" draw:$j 2>&1 | tail -1)
  echo "draw $j $(cut -d' ' -f3- "$W/draw_$j.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$j.txt"
  grep '^BENCHRES' "$W/draw_$j/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$j.txt"; }
for j in 1 2; do run $(( 9000 + 1000*H + 100*k + 2*S + j )) & done; wait
cat "$OUT"/draw_*.txt >> "$OUT/task.txt"
