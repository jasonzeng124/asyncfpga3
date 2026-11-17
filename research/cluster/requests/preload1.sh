#!/bin/bash
#CLUSTER array=1-68 cores=8 mem=32G time=150
# preload1: xorshift's incrementer judged by draws through a PRELOADED loop state (research/data/preload/README.md).
# x55a10 sizes with UADDI0 = 12 / 8 / 6 / 4 (tasks 1-16 / 17-32 / 33-48 / 49-64; route = seed = (TASK-1)%16+1), 4 draws
# each (K = 100S+1..4, the default model as in cand3; the UADDI0 12 arm is cand3's own routes and draws), on xp1 =
# xor19's 19 vectors (natural state) + 10 preloaded rows whose counter crosses 2^k-1 -> 2^k for k = 8, 12, 16, 24, 30,
# the 2^31-3 start, the 32-bit wrap -1 -> 0, and 81 iterations across 2^30 (oracle: kernels/xorshift/xorshift.c from
# the same state, research/tools/preload/preload_oracle.sh). Preload = force of the two entry latches' output nets
# (ulink_n6 = i0, ulink_n_trueResult_2 = n) per batch: research/tools/preload/gen_preload.py via build_ps.sh's PS_MON_GEN.
# Tasks 65-68 (control, must FAIL): the UADDI0 12 arm on routes 1-4 with the adder's sum bits 16-31 -> their latch made
# +8000 ps late (SDF only, research/tools/fifteen/sdf_inject.py), 1 draw each on pre1 (the preloaded rows alone): bits
# 16-31 of i+1 never toggle on xor19 (i < 1000), so only the preloaded rows (k = 16, 24, 30, wrap) can see the defect.
# PREDICTION: every arm, 12 / 8 / 6 / 4, passes every draw on EQUIVALENT routes (256 / 256): locally on route 21 even
# UADDI0 = 1 passed pre1 and xor19 at worst, because i + 1 is joined (ucond_br6_j) with i < n, whose compare ripples the
# same 32 bits behind its own delay, so the incrementer's line is not what covers its carry. P per arm within 0.3 ns of
# the 12 arm (the compare, not the incrementer, sets the join). Control tasks 65-68: FAIL on every route, the k = 16 / 24 /
# 30 / wrap rows wrong or hung, the k = 8 / 12 rows and the two i0 = 0 rows right.
set -uo pipefail
if [ $TASK -gt 64 ]; then CTL=1; A=0; S=$(( TASK - 64 )); else CTL=0; A=$(( (TASK - 1) / 16 )); S=$(( (TASK - 1) % 16 + 1 )); fi
G=research/data/eventgraph/gate; K=xorshift
case $A in 0) U=12; Z=research/data/xorshift_sizes_T3s50_fr4a_x55a10_bench.vh;;
           *) U=$(( A == 1 ? 8 : A == 2 ? 6 : 4 )); Z=research/data/preload/xorshift_sizes_x55a10_add$U.vh;; esac
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir
NM=pl1_a${U}_$S; [ $CTL = 1 ] && NM=pl1_ctl_$S
echo "x55a10 UADDI0 $U seed $S" > "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $S research/data/fifteen/vec_xorshift.hex $G/xor19.hex $G/xor19.exp \
  BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
md5sum "$HW/$D.sdf" "$RD/xray.sdf" >> "$OUT/task.txt"; head -2 "$OUT/eval.txt" >> "$OUT/task.txt"
if [ $CTL = 1 ]; then
  python3 research/tools/fifteen/sdf_inject.py "$RD/xray.sdf" "$RUNS/inj.sdf" 'slice\[[4-7]\]\.genblk1\.carry4/O' 'ulink_n_trueResult_6\.many\.stage\[0\]\.' 8000 > "$OUT/inject.txt" 2>&1 || { echo "nothing injected" >> "$OUT/task.txt"; exit 1; }
  k=$(( 100*S + 1 )); W=$RUNS/d/$k; mkdir -p "$W"
  r=$(GATE_TBATCH=30000 timeout 100m research/tools/preload/preload_gate.sh "$HW" "$W" "$RUNS/inj.sdf" pre1 draw:$k 2>&1 | tail -1)
  echo "CONTROL inj16 +8000 draw $k $(cut -d' ' -f3- "$W/draw_$k.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$k.txt"
  grep -E '^BENCHRES|^PRELOAD' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$k.txt"
  cat "$OUT/draw_$k.txt" >> "$OUT/task.txt"; exit 0
fi
python3 research/tools/ffmux_scan.py "$HW/$D.fasm" > /dev/null 2>&1 && echo ffmux-clean >> "$OUT/task.txt" || echo FFMUX-FLAG >> "$OUT/task.txt"
run() { k=$1; W=$RUNS/d/$k; mkdir -p "$W"
  r=$(timeout 100m research/tools/preload/preload_gate.sh "$HW" "$W" "$RD/xray.sdf" xp1 draw:$k 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3- "$W/draw_$k.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$k.txt"
  grep -E '^BENCHRES|^PRELOAD' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$k.txt"; }
for j in 1 2 3 4; do run $(( 100*S + j )) & done; wait
cat "$OUT"/draw_*.txt >> "$OUT/task.txt"
