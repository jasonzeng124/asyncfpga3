#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# cand3: item 35's sizes with UCMPI0 6 -> 10 (x55a10; formal C41: at CARRY/F7 1.0 x55a keeps ~0 ps at the loop-entry steer
# ucond_br2, x55a10 >= 387 ps on 8 routes, no visible cost). Routes 1-32; per route 4 default draws (K = 100S+1..4, the model
# as in shrink5) and 4 slow-carry draws (K = 100S+51..54, DRAW_CARRY=0.8,1.0: CARRY4 / F7F8 / FF only in the top fifth of
# the band, which no August latency can exclude). PREDICTION: 256 / 256 on EQUIVALENT routes; P median 16.85 +- 0.2 ns
# (shrink5 x55a); the slow-carry half is the new information.
set -uo pipefail
S=$TASK; G=research/data/eventgraph/gate; K=xorshift; V=xor19
Z=research/data/xorshift_sizes_T3s50_fr4a_x55a10_bench.vh
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir
NM=c3_x55a10_$S
echo "x55a10 seed $S" > "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $S research/data/fifteen/vec_xorshift.hex $G/$V.hex $G/$V.exp \
  BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
md5sum "$HW/$D.sdf" "$RD/xray.sdf" >> "$OUT/task.txt"; head -2 "$OUT/eval.txt" >> "$OUT/task.txt"
run() { k=$1; W=$RUNS/d/$k; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
  r=$(timeout 100m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" draw:$k 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3- "$W/draw_$k.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$k.txt"
  grep '^BENCHRES' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$k.txt"; }
for j in 1 2 3 4; do run $(( 100*S + j )) & done; wait
for j in 1 2 3 4; do DRAW_CARRY=0.8,1.0 run $(( 100*S + 50 + j )) & done; wait
cat "$OUT"/draw_*.txt >> "$OUT/task.txt"
