#!/bin/bash
#CLUSTER array=1-64 cores=8 mem=32G time=240
# shrink7: shrink6's x0.55s (arithmetic kept) gave 21.30 ns, no gain: the 3n+1 delay IS collatz's cycle. Instead put the
#   long carries into the vectors: col17 = col14 + n = 77671, 94959, 109881, whose trajectories peak at 1570824736 (31 bits),
#   720170836, 593279152 (the highest peaks below 113383, where int32 trajectories end). x0.55 and x0.70 of EVERY size,
#   routes 1-32, 4 draws each.
# (was) shrink6: collatz candidate -- item 31's sizes x0.55 except the arithmetic whose long carries no vector reaches
#   (USELECT0 = 3n+1 / n>>1, UADDI0, UADDI1 kept), routes 1-32, 4 draws each on col14. (shrink2: x0.55 of everything
#   passed 32/32 draws on 4 routes.) Header of shrink2 follows.
# shrink2 (PROGRAM 2026-11-16: "sizes may be chosen by this simulation"): collatz item 31 (fcsel3a, sizes nl6s3a) with every matched
# delay scaled by f = 0.85 / 0.70 / 0.55 (research/tools/shrink_sizes.py, ceil, floor 1), on routes 20 (the board
# seed), 3, 7, 12; each route 8 draws of the delay model (bench_gate.sh draw:K, fixed verdict) on col14. Result per f: the
# period (event graph), the fraction of draws passing, and fasm_equiv / ffmux. Task = f x route.
set -uo pipefail
FS=(55 70); F=${FS[$(( (TASK-1) / 32 ))]}; S=$(( (TASK-1) % 32 + 1 ))
G=research/data/eventgraph/gate; K=collatz; V=col17
Z=research/data/collatz_sizes_T3cdb_nl6s3a_x${F}_bench.vh
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz_preeq2.mlir
NM=s7_x${F}_$S
echo "factor 0.$F seed $S sizes $Z" > "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $S research/data/fifteen/vec_collatz.hex $G/$V.hex $G/$V.exp \
  BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
cp "$OUT/eval.txt" "$OUT/eval_build.txt" 2>/dev/null
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
head -2 "$OUT/eval.txt" >> "$OUT/task.txt"
run() { k=$1; W=$RUNS/d/$k; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
  r=$(timeout 100m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" draw:$k 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3- "$W/draw_$k.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$k.txt"
  grep '^BENCHRES' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$k.txt"; }
for j in 1 2 3 4; do run $(( 100*S + j )) & done; wait
cat "$OUT"/draw_*.txt >> "$OUT/task.txt"
