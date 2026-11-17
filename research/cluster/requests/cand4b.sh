#!/bin/bash
#CLUSTER array=1-10 cores=8 mem=32G time=240
# cand4: the collatz and ipow candidates chosen by the draws (x0.55 fails draws on clean routes: collatz route 30 at CARRY
# 0.75 / 0.91, ipow route 12 at CARRY 0.20 too; x0.70 passed every draw: collatz 96/96 on 24 EQUIVALENT routes, P median 19.76 ns;
# ipow 84/84 on 21 EQUIVALENT routes, P median 30.21). Board route = the median EQUIVALENT ffmux-clean route: collatz x0.70
# seed 27 (P 19.77), ipow x0.70 seed 31 (P 30.21). Tasks 1-4 / 6-9: 32 default draws (K = 7000 + 1000c + n); tasks 5 / 10:
# the gate at SLOW_MAX / FAST_MIN / worst. PREDICTION: 32/32 and 3/3 for both.
set -uo pipefail
C=$(( (TASK-1) / 5 )); B=$(( (TASK-1) % 5 ))
G=research/data/eventgraph/gate
CENV="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
IENV="BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
case $C in
  0) N=cx70; K=collatz; S=27; Z=research/data/collatz_sizes_T3cdb_nl6s3a_x70_bench.vh; V=col18; E=$CENV
     export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz_preeq2.mlir;;
  1) N=ix70; K=ipow; S=31; Z=research/data/ipow_dsp1_sizes_T9s75_h4s3m_x70_bench.vh; V=ipow17; E=$IENV;;
esac
NM=c4_${N}_$S
echo "candidate c$C $N kernel $K seed $S block $B vectors $V" > "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $S research/data/fifteen/vec_$K.hex $G/$V.hex $G/$V.exp $E > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
md5sum "$HW/$D.sdf" "$HW/$D.bit" "$RD/xray.sdf" >> "$OUT/task.txt"; head -2 "$OUT/eval.txt" >> "$OUT/task.txt"
if [ $B -eq 4 ]; then
  for C2 in max min worst; do
    ( W=$RUNS/g/$C2; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/"
      r=$(timeout 150m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" $C2 2>&1 | tail -1)
      echo "gate $V $C2 ${r:-TIMEOUT/none}" > "$OUT/gate_$C2.txt"
      grep '^BENCHRES' "$W/$C2/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$C2.txt" ) &
  done; wait; cat "$OUT"/gate_*.txt >> "$OUT/task.txt"; exit 0
fi
run() { k=$1; W=$RUNS/d/$k; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
  r=$(timeout 100m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" draw:$k 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3- "$W/draw_$k.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$k.txt"
  grep '^BENCHRES' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$k.txt"; }
for w in 0 1; do for j in 1 2 3 4; do run $(( 7000 + 1000*C + B*8 + w*4 + j )) & done; wait; done
cat "$OUT"/draw_*.txt >> "$OUT/task.txt"
