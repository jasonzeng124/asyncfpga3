#!/bin/bash
#CLUSTER array=1-33 cores=8 mem=48G time=180
# (research lead, 2026-11-17: the x0.70 half -- old tasks 33-64 -- is dropped before submission: PROGRAM "General first"
#  forbids new per-kernel shrink sweeps. Task 33 = the old task 65, the three corners on route 1.)
# gcddraw1 (PROGRAM 2026-11-17 "Use the quota" item 7: gcd judged by draws, like the other four). gcd's board candidates
# (BOARD-QUEUE list #1 gcd_ps P1, #3 = item 5 gcd_hw R5s75 + fast fall) are build_hw.sh rigs that the draw machinery
# cannot run; this judges the same compiled kernel and the same per-cell sizes on the kernel bench (gcd_bench_gen, PS7
# host, the harness every other kernel is judged on), built by eval_task.sh exactly as the others. Recipe = BQ item 5's:
# sizes gcd_hw_sizes_R5s75.vh with the bench's macro prefix (research/data/gcd_draws/gcd_bench_sizes_R5s75.vh, 220
# sizes, the same numbers), BDC_LINK_FASTFALL=1, gcd_hw_pads.json select pads, v4 placement (place weight 1, column
# rows 9, as build_hw.sh defaults them). Vectors gcd18 (inside the bench mask a, b & 0x7FFFFFFF; oracle compiled from
# Dynamatic's gcd.c by research/data/gcd_draws/gcd_oracle.sh; a == b, operand 1, operand 0, coprime Fibonacci pair,
# powers of two, 0x7FFFFFFF, the longest in-domain pairs (31 main-loop iterations + 59 shifts); no answer is 0 and no
# two consecutive answers are equal, so a result stream one call behind cannot pass).
# Tasks 1-32: R5s75 on routes 1-32; tasks 33-64: R5s75 x0.70 (shrink_sizes.py; = R5 x ~0.53) on the same routes and the
# same draw numbers K = 100*route + j (paired draws). 4 draws each. Task 65: R5s75 route 1 (the local route) at the three
# fixed corners (SLOW_MAX / FAST_MIN / worst), which could not be run locally (the shared machine OOM-killed gcd's 5 GB
# vvp twice). PREDICTION task 65: 3/3 PASS.
# Local reference (research/data/gcd_draws/README.md): R5s75 route 1 (sdf 5c1abff4, EQUIVALENT, ffmux-clean, P 87.2 ns per
# main iteration + shift): draws 101 and 102 PASS 18/18 (5522 / 5366 cycles); tasks 1 and 65 repeat that route.
# PREDICTION: R5s75 passes every draw on every EQUIVALENT ffmux-clean route (128/128 less excluded routes): it passed
# the old worst-case gate and both corners on 8 gcd_hw routes, and draws sit between FAST_MIN and that worst case.
# x0.70: passes >= 124/128 (xorshift / collatz / ipow all held at x0.70 of their sizes; gcd's R5s75 is already x0.75, so
# this is x0.53 of R5, near where xorshift (x0.40a) and collatz/ipow (x0.55) first lost draws: a few failing routes would
# not surprise). Period (event graph, vector 7fffffff 00000001): x0.70 shorter than R5s75 by ~15-25%.
# eval_task.sh with TSE_ONLY=1 and no TSE_VEC = the build (lane2.sh: bench build, fasm_equiv, ffmux, event-graph period)
# and nothing else: the static corner_audit (STATIC_ONLY's step) did not finish in 55 min on gcd locally and is not a gate (PROGRAM
# 2026-11-16). Memory: gcd's gate compile (iverilog) peaks at ~9.3 GB and each draw's vvp holds ~5.1 GB (xorshift 2.4):
# 48G for 4 draws + 1 compile (compiles are serialised by bench_gate.sh's flock). Locally one draw = ~20 min.
set -uo pipefail
FS=(75 75x70); H=0; S=$TASK; CORNERS=0
[ $TASK = 33 ] && { H=0; S=1; CORNERS=1; }
G=research/data/eventgraph/gate; K=gcd; V=gcd18
Z=research/data/gcd_draws/gcd_bench_sizes_R5s75.vh; [ $H = 1 ] && Z=research/data/gcd_draws/gcd_bench_sizes_R5s75_x70.vh
NM=gd1_${FS[$H]}_$S
echo "gcd sizes ${FS[$H]} seed $S sizes $Z$([ $CORNERS = 1 ] && echo " corners")" > "$OUT/task.txt"
TSE_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $S research/data/gcd_draws/vec_gcd.hex $G/$V.hex $G/$V.exp \
  BDC_LINK_FASTFALL=1 BD_RLOC=v4 BD_PLACE_WEIGHT=1 BD_COLUMN_ROWS=9 BDC_SELECT_PADS=$PWD/cells/hw/gcd_hw_pads.json \
  > "$OUT/log_eval.txt" 2>&1
cp "$OUT/eval.txt" "$OUT/eval_build.txt" 2>/dev/null
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
md5sum "$HW/$D.sdf" "$RD/xray.sdf" >> "$OUT/task.txt"; head -2 "$OUT/eval.txt" >> "$OUT/task.txt"
if [ $CORNERS = 1 ]; then
  for C in max min worst; do W=$RUNS/g/$C; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/"
    r=$(timeout 100m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" $C 2>&1 | tail -1)
    echo "gate $V $C ${r:-TIMEOUT/none}" > "$OUT/gate_$C.txt"
    grep '^BENCHRES' "$W/$C/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$C.txt"
  done; cat "$OUT"/gate_*.txt >> "$OUT/task.txt"; exit 0
fi
run() { k=$1; W=$RUNS/d/$k; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
  r=$(timeout 100m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" draw:$k 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3- "$W/draw_$k.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$k.txt"
  grep '^BENCHRES' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$k.txt"; }
for j in 1 2 3 4; do run $(( 100*S + j )) & done; wait
cat "$OUT"/draw_*.txt >> "$OUT/task.txt"
