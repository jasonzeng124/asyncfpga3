#!/bin/bash
#CLUSTER array=1-64 cores=8 mem=32G time=240
# shrink10 (PROGRAM 2026-11-17 lead 4): collatz64 by draws on c6419 (in-domain vectors whose trajectories peak at 48-49 bits,
# plus n = 1). Item 32's sizes (fc64sel3p, h4s3p; 31.4 ns) x 0.70 and x 0.55 of EVERY size, routes 1-32, 4 default draws each
# (K = 100S + 10f + j). PREDICTION (from collatz shrink9 / ipow shrink8): x0.70 128/128 on EQUIVALENT routes, P median ~27 ns;
# x0.55 loses draws on a route or two.
set -uo pipefail
FS=(55 70); F=${FS[$(( (TASK-1) / 32 ))]}; S=$(( (TASK-1) % 32 + 1 ))
G=research/data/eventgraph/gate; K=collatz64; V=c6419
Z=research/data/collatz64_sizes_T4cdb_h4s3p_x${F}_bench.vh
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir
NM=s10_x${F}_$S
echo "factor 0.$F seed $S sizes $Z" > "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $S research/data/fifteen/vec_collatz.hex $G/$V.hex $G/$V.exp \
  BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
head -2 "$OUT/eval.txt" >> "$OUT/task.txt"
run() { k=$1; W=$RUNS/d/$k; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
  r=$(timeout 100m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" draw:$k 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3- "$W/draw_$k.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$k.txt"
  grep '^BENCHRES' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$k.txt"; }
for j in 1 2 3 4; do run $(( 100*S + 10*(F/10) + j )) & done; wait
cat "$OUT"/draw_*.txt >> "$OUT/task.txt"
