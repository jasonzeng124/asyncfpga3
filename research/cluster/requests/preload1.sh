#!/bin/bash
#CLUSTER array=1-64 cores=8 mem=32G time=150
# preload1: xorshift's incrementer judged by draws through a PRELOADED loop state (research/data/preload/README.md).
# x55a10 sizes with UADDI0 = 12 / 8 / 6 / 4 (tasks 1-16 / 17-32 / 33-48 / 49-64; route = seed = (TASK-1)%16+1), 4 draws
# each (K = 100S+1..4, the default model as in cand3; the UADDI0 12 arm is cand3's own routes and draws), on xp1 =
# xor19's 19 vectors (natural state) + 10 preloaded rows whose counter crosses 2^k-1 -> 2^k for k = 8, 12, 16, 24, 30,
# the 2^31-3 start, the 32-bit wrap -1 -> 0, and 81 iterations across 2^30 (oracle: kernels/xorshift/xorshift.c from
# the same state, research/tools/preload/preload_oracle.sh). Preload = force of the two entry latches' output nets
# (ulink_n6 = i0, ulink_n_trueResult_2 = n) per batch: research/tools/preload/gen_preload.py via build_ps.sh's PS_MON_GEN.
# PREDICTION: see the PREDICTION line below (filled from the local negative control on route 21).
set -uo pipefail
A=$(( (TASK - 1) / 16 )); S=$(( (TASK - 1) % 16 + 1 )); G=research/data/eventgraph/gate; K=xorshift
case $A in 0) U=12; Z=research/data/xorshift_sizes_T3s50_fr4a_x55a10_bench.vh;;
           *) U=$(( A == 1 ? 8 : A == 2 ? 6 : 4 )); Z=research/data/preload/xorshift_sizes_x55a10_add$U.vh;; esac
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir
NM=pl1_a${U}_$S
echo "x55a10 UADDI0 $U seed $S" > "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $S research/data/fifteen/vec_xorshift.hex $G/xor19.hex $G/xor19.exp \
  BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
md5sum "$HW/$D.sdf" "$RD/xray.sdf" >> "$OUT/task.txt"; head -2 "$OUT/eval.txt" >> "$OUT/task.txt"
python3 research/tools/ffmux_scan.py "$HW/$D.fasm" > /dev/null 2>&1 && echo ffmux-clean >> "$OUT/task.txt" || echo FFMUX-FLAG >> "$OUT/task.txt"
run() { k=$1; W=$RUNS/d/$k; mkdir -p "$W"
  r=$(timeout 100m research/tools/preload/preload_gate.sh "$HW" "$W" "$RD/xray.sdf" xp1 draw:$k 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3- "$W/draw_$k.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$k.txt"
  grep -E '^BENCHRES|^PRELOAD' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$k.txt"; }
for j in 1 2 3 4; do run $(( 100*S + j )) & done; wait
cat "$OUT"/draw_*.txt >> "$OUT/task.txt"
