#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# shrink4 (after shrink1: item 33's sizes x0.40 passed 8/8 draws on its board route; every failure at x0.55 was on a route
# with the 5FF-D bitstream defect). Two questions:
#  tasks 1-6: where the draws first fail -- every size x0.30 / 0.20 / 0.10 (x0.10 = nearly every line at 1), routes 2 and 5,
#    8 draws each;
#  tasks 7-38: the board candidates -- x0.40a and x0.30a = every size scaled EXCEPT the loop counter's add and the two
#    compares (UADDI0, UCMPI0, UCMPI1 kept: their 32-bit carries are beyond any simulated vector; the full-range rule of
#    2026-11-14), routes 1-16 each, 4 draws per route (64 per candidate). Vectors xor19, the fixed verdict.
# shrink4: shrink3's x0.40c kept the loop counter's add AND both compares; it cost most of the gain (median ~18.6 ns).
#   The compares' long carry IS simulated: every loop's last test compares i = n-2 with n-1, equal in every upper bit, so
#   the chain ripples the full width. Only i + 1's long carry (i = 2^k - 1, k > 9) is beyond the vectors. x0.40a / x0.30a:
#   every size scaled except UADDI0 (12). Routes 1-16, 4 draws each, xor19, the fixed verdict.
set -uo pipefail
i=$((TASK-1)); [ $i -lt 16 ] && F=40a || F=30a; S=$(( i % 16 + 1 )); ND=4
G=research/data/eventgraph/gate; K=xorshift; V=xor19
Z=research/data/xorshift_sizes_T3s50_fr4a_x${F}_bench.vh
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir
NM=s4_x${F}_$S
echo "factor $F seed $S sizes $Z" > "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $S research/data/fifteen/vec_xorshift.hex $G/$V.hex $G/$V.exp \
  BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
head -2 "$OUT/eval.txt" >> "$OUT/task.txt"
run() { k=$1; W=$RUNS/d/$k; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
  r=$(timeout 100m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" draw:$k 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3- "$W/draw_$k.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$k.txt"
  grep '^BENCHRES' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$k.txt"; }
# draws differ per route (draw number = 100*seed + j) so the 64 draws of a candidate are 64 distinct model draws
for w in 0 1; do for j in 1 2 3 4; do n=$(( w*4 + j )); [ $n -le $ND ] && run $(( 100*S + n )) & done; wait; done
cat "$OUT"/draw_*.txt >> "$OUT/task.txt"
