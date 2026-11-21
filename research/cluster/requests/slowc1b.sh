#!/bin/bash
#CLUSTER array=1-20 cores=8 mem=32G time=240
# slowc1 (PROGRAM 2026-11-17 "where does the board sit"): no August board latency pins the CARRY4 / F7F8 / FF band (own
# runs, audit T145, formal A13), so the board candidates are re-judged at its slow end: 16 draws each on the board route
# with DRAW_CARRY=0.8,1.0 (chains and rest drawn as usual). K = 5000 + 100c + n. Task = candidate c (0-9) x block of 8.
#   c0 item 33 fxa s27 | c1 item 27 fxd s2 | c2 item 31 fcsel3a s20 | c3 item 28 fcsel3m s20 | c4 item 29 fisel3m s19 |
#   c5 item 30 fc64sel3 s10 | c6 item 32 fc64sel3p s22 | c7 item 35 fr4a_x55a s21 |
#   c8 collatz x0.70 (shrink9 median EQUIVALENT route, s27) | c9 ipow x0.70 (shrink8 median EQUIVALENT route, s31)
# PREDICTION: items 33 / 27 / 31 / 28 / 29 / 30 / 32 16/16 (full sizes); item 35 loses draws (formal C36/C38: its loop-entry
# steer has ~0 ps at CARRY 0.9-1.0; own audit T144 60 ps); c8 / c9 16/16.
set -uo pipefail
C=$(( (TASK-1) / 2 )); B=$(( (TASK-1) % 2 ))
G=research/data/eventgraph/gate
XENV="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0"
CENV="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
IENV="BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
case $C in
  0) N=fxa; K=xorshift; S=27; Z=research/data/xorshift_sizes_T3s50_fr4a_bench.vh; V=xor19; E=$XENV;;
  1) N=fxd; K=xorshift; S=2; Z=research/data/xorshift_sizes_T3s50_fr4_bench.vh; V=xor19; E=$XENV;;
  2) N=fcsel3a; K=collatz; S=20; Z=research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh; V=col18; E=$CENV;;
  3) N=fcsel3m; K=collatz; S=20; Z=research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh; V=col18; E=$CENV;;
  4) N=fisel3m; K=ipow; S=19; Z=research/data/ipow_dsp1_sizes_T9s75_h4s3m_bench.vh; V=ipow17; E=$IENV;;
  5) N=fc64sel3; K=collatz64; S=10; Z=research/data/collatz64_sizes_T4cdb_h4s3_bench.vh; V=c6419; E=$CENV;;
  6) N=fc64sel3p; K=collatz64; S=22; Z=research/data/collatz64_sizes_T4cdb_h4s3p_bench.vh; V=c6419; E=$CENV;;
  7) N=x55a; K=xorshift; S=21; Z=research/data/xorshift_sizes_T3s50_fr4a_x55a_bench.vh; V=xor19; E=$XENV;;
  8) N=cx70; K=collatz; S=27; Z=research/data/collatz_sizes_T3cdb_nl6s3a_x70_bench.vh; V=col18; E=$CENV;;
  9) N=ix70; K=ipow; S=31; Z=research/data/ipow_dsp1_sizes_T9s75_h4s3m_x70_bench.vh; V=ipow17; E=$IENV;;
esac
case $K in xorshift) export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir;;
           collatz|collatz64) export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/${K}_preeq2.mlir;; esac
NM=sc_${N}_$S
echo "candidate c$C $N kernel $K seed $S block $B vectors $V carry 0.8-1.0" > "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $S research/data/fifteen/vec_${K%64}.hex $G/$V.hex $G/$V.exp $E > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
md5sum "$HW/$D.sdf" "$RD/xray.sdf" >> "$OUT/task.txt"; head -2 "$OUT/eval.txt" >> "$OUT/task.txt"
run() { k=$1; W=$RUNS/d/$k; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
  r=$(DRAW_CARRY=0.8,1.0 timeout 100m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" draw:$k 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3- "$W/draw_$k.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$k.txt"
  grep '^BENCHRES' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$k.txt"; }
for w in 0 1; do for j in 1 2 3 4; do run $(( 5000 + 100*C + B*8 + w*4 + j )) & done; wait; done
cat "$OUT"/draw_*.txt >> "$OUT/task.txt"
