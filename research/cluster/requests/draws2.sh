#!/bin/bash
#CLUSTER array=1-5 cores=8 mem=32G time=240
# draws2: the xorshift candidate chosen by the draws (shrink5): item 33's sizes x0.55 except UADDI0 (fr4a_x55a; 128/128 draws
# on 32 routes, median 16.85 ns; x0.50a ties at 16.74 so the longer is taken; x0.40a fails on routes 12 and 14). Its board
# route, seed 21 (P 16.84 = the median, EQUIVALENT, ffmux-clean): tasks 1-4 = draws 2101-2132 (8 each), task 5 = the gate at
# SLOW_MAX / FAST_MIN / worst on xor17 and xor19, the fixed verdict.
set -uo pipefail
G=research/data/eventgraph/gate; K=xorshift; S=21; Z=research/data/xorshift_sizes_T3s50_fr4a_x55a_bench.vh
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir
NM=d2_x55a_$S
echo "x55a seed $S task $TASK" > "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $S research/data/fifteen/vec_xorshift.hex $G/xor19.hex $G/xor19.exp \
  BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
md5sum "$HW/$D.sdf" "$HW/$D.bit" "$RD/xray.sdf" >> "$OUT/task.txt"; head -2 "$OUT/eval.txt" >> "$OUT/task.txt"
if [ $TASK -eq 5 ]; then
  for V in xor17 xor19; do for C in max min worst; do
    ( W=$RUNS/g/$V/$C; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/"
      r=$(timeout 120m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" $C 2>&1 | tail -1)
      echo "gate $V $C ${r:-TIMEOUT/none}" > "$OUT/gate_${V}_$C.txt"
      grep '^BENCHRES' "$W/$C/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_${V}_$C.txt" ) &
  done; done; wait; cat "$OUT"/gate_*.txt >> "$OUT/task.txt"; exit 0
fi
run() { k=$1; W=$RUNS/d/$k; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
  r=$(timeout 100m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/xor19.hex" "$G/xor19.exp" draw:$k 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3- "$W/draw_$k.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$k.txt"
  grep '^BENCHRES' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$k.txt"; }
for w in 0 1; do for j in 1 2 3 4; do run $(( 2100 + (TASK-1)*8 + w*4 + j )) & done; wait; done
cat "$OUT"/draw_*.txt >> "$OUT/task.txt"
