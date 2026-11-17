#!/bin/bash
#CLUSTER array=1-64 cores=8 mem=32G time=240
# sizerule1 (PROGRAM "General first" item 2: sizes from one rule, not a factor per kernel; research/data/sizerule/README.md).
# The rule: research/tools/corner_audit.py with CA_SIZERULE=1 -- chains and LUT/wire at ONE band (0.21; the default
# corner put chains at 0.21 and the data's LUTs/wires at 0.288), CARRY4/F7F8/FF still at SLOW_MAX (unmeasured), the
# residual guards unchanged (0.97/1.03, max(0.03 t, 50 ps)), a shortened line priced at its own mean link step and the
# route's most compact whole chain (not the single cheapest hop), select paths sized by E/M like any line, and never
# below the largest size that failed a draw: every line the failing file shortened keeps its failing size, +1 on the lines
# the static check named on the failing routes (research/data/sizerule/floor_<kernel>.vh, research/tools/sizerule_floor.py). Same rule, same flags, every kernel; no factor.
# Task = kernel (4) x route 1-16. Per task: (1) build the item's sizes on seed S (xorshift 33 fr4a, collatz 31 nl6s3a,
# ipow 29 h4s3m, collatz64 32 h4s3p); (2) corner_audit CA_SIZERULE=1 on that route -> this route's sizes; (3) rebuild
# seed S with them (P, fasm_equiv, ffmux; the default static rule at nom/worst, report only); (4) 4 default draws
# (K = 20000 + 1000c + 10S + j) and the `worst` gate (chains 0.21 vs rest 0.288, carry 1, M scatter: the chain/rest
# mismatch corner the rule no longer sizes for). The per-cell max over the 16 routes' proposals (sr1_prop.vh, back in
# OUT) is the file for the next round: research/tools/fifteen/max_sizes.py.
# PREDICTION: the rule's proposals sit at ~0.45-0.6 of the item sizes on the lines that set the cycle (xorshift
#   uxori/ucmpi/umux at or near the x0.40a+1 floor; collatz uaddi0/uselect0 4-6 vs 9/7; ipow ushrsi0 ~10-13 vs 23,
#   ucmpi2 ~6-10 vs 18, umuli1 ~20-26 vs 36; collatz64 uaddi0 ~10-14 vs 23); on EQUIVALENT ffmux-clean routes every
#   default draw passes (>= 60/62 per kernel; a failure is most likely a carry-heavy compare at CARRY >= 0.75, as collatz
#   x0.55 route 30); the `worst` gate passes on >= 14/16 per kernel; P median within 0.5 ns of x0.55 (xorshift 16.85) /
#   x0.70 (collatz 19.6, ipow 30.2) or below. A `worst`-gate failure with every draw passing says the chain/rest
#   mismatch is real on this die model and the band merge (part 1 of the rule) is what to take back.
set -uo pipefail
C=$(( (TASK-1) / 16 )); S=$(( (TASK-1) % 16 + 1 ))
G=research/data/eventgraph/gate
unset MLIR_OVERRIDE BD_SKEW_AND_JOIN
case $C in
  0) K=xorshift; V=xor19; Z=research/data/xorshift_sizes_T3s50_fr4a_bench.vh; VEC=vec_xorshift.hex
     export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir
     E="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0";;
  1) K=collatz; V=col18; Z=research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh; VEC=vec_collatz.hex
     export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz_preeq2.mlir
     E="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0";;
  2) K=ipow; V=ipow17; Z=research/data/ipow_dsp1_sizes_T9s75_h4s3m_bench.vh; VEC=vec_ipow.hex
     E="BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0";;
  3) K=collatz64; V=c6419; Z=research/data/collatz64_sizes_T4cdb_h4s3p_bench.vh; VEC=vec_collatz.hex
     export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir
     E="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0";;
esac
D=${K}_bench_gen; N0=sr1b_${K}_$S; N1=sr1_${K}_$S
echo "sizerule1 kernel $K seed $S base $Z vectors $V" > "$OUT/task.txt"
# (1) the base build only (TSE_ONLY without TSE_VEC: build + corner_audit's route dir, no audits)
mkdir -p "$OUT/b0"
OUT="$OUT/b0" TSE_ONLY=1 research/tools/fifteen/eval_task.sh $N0 $K $Z $S research/data/fifteen/$VEC $G/$V.hex $G/$V.exp $E > "$OUT/log_b0.txt" 2>&1
CA=$RUNS/ca/$N0
[ -f "$CA/seed1/pnr/soak_routed.json" ] || { echo "base build failed" >> "$OUT/task.txt"; exit 1; }
head -1 "$OUT/b0/eval.txt" >> "$OUT/task.txt"
# (2) the rule on this route
CA_SIZERULE=1 CA_SIZERULE_FLOOR=research/data/sizerule/floor_$K.vh python3 research/tools/corner_audit.py "$CA/seed1" \
  --prefix bridge_i.udut. --out "$CA/sr1" > "$OUT/sr1_proposal.txt" 2>&1
[ -f "$CA/sr1/sizes.vh" ] || { echo "sizerule corner_audit failed" >> "$OUT/task.txt"; exit 1; }
cp "$CA/sr1/sizes.vh" "$OUT/sr1_prop.vh"; cp "$CA/sr1/lines.tsv" "$OUT/sr1_lines.tsv"; head -40 "$CA/sr1/report.txt" > "$OUT/sr1_report_head.txt"
Z1=research/data/sizerule/run_${K}_$S.vh; cp "$CA/sr1/sizes.vh" "$Z1"
grep -c "was" "$Z1" | sed 's/^/lines changed /' >> "$OUT/task.txt"
# (3) rebuild with the rule's sizes (build, fasm_equiv, ffmux, event-graph period; no sizing round)
TSE_ONLY=1 research/tools/fifteen/eval_task.sh $N1 $K $Z1 $S research/data/fifteen/$VEC $G/$V.hex $G/$V.exp $E > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$N1; RD=$RUNS/r/$N1; CA1=$RUNS/ca/$N1
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
md5sum "$HW/$D.sdf" >> "$OUT/task.txt"; head -2 "$OUT/eval.txt" >> "$OUT/task.txt"
# (4) 4 default draws + the worst gate + the default static rule (report only) at worst and nom, in parallel
for m in worst nom; do X=""; [ $m = nom ] && X="--uniform 0.288"
  ( python3 research/tools/corner_audit.py "$CA1/seed1" --prefix bridge_i.udut. $X --no-size --out "$CA1/st_$m" > "$OUT/static_$m.log" 2>&1
    sed -n '/^NEGATIVE/,/^$/p' "$CA1/st_$m/report.txt" > "$OUT/static_neg_$m.txt" 2>/dev/null ) &
done
run() { k=$1; W=$RUNS/d/$k; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
  r=$(timeout 100m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" draw:$k 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3- "$W/draw_$k.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$k.txt"
  grep '^BENCHRES' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$k.txt"; }
for j in 1 2 3 4; do run $(( 20000 + 1000*C + 10*S + j )) & done
( W=$RUNS/g/$N1/worst; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/"
  r=$(timeout 100m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" worst 2>&1 | tail -1)
  echo "gate $V worst ${r:-TIMEOUT/none}" > "$OUT/gate_worst.txt" ) &
wait
cat "$OUT"/draw_*.txt "$OUT/gate_worst.txt" >> "$OUT/task.txt"
