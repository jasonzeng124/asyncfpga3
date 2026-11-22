#!/bin/bash
#CLUSTER array=1-12 cores=8 mem=32G time=240
# shrink2 (PROGRAM 2026-11-16: "sizes may be chosen by this simulation"): collatz item 31 (fcsel3a, sizes nl6s3a) with every matched
# delay scaled by f = 0.85 / 0.70 / 0.55 (research/tools/shrink_sizes.py, ceil, floor 1), on routes 20 (the board
# seed), 3, 7, 12; each route 8 draws of the delay model (bench_gate.sh draw:K, fixed verdict) on col14. Result per f: the
# period (event graph), the fraction of draws passing, and fasm_equiv / ffmux. Task = f x route.
set -uo pipefail
FS=(85 70 55); SS=(20 3 7 12)
F=${FS[$(( (TASK-1) / 4 ))]}; S=${SS[$(( (TASK-1) % 4 ))]}
G=research/data/eventgraph/gate; K=collatz; V=col14
Z=research/data/collatz_sizes_T3cdb_nl6s3a_x${F}_bench.vh
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz_preeq2.mlir
NM=sc_x${F}_$S
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
for w in 0 1; do for j in 1 2 3 4; do run $(( w*4 + j )) & done; wait; done
cat "$OUT"/draw_*.txt >> "$OUT/task.txt"
