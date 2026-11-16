#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# draws1 (PROGRAM 2026-11-16 "the board decides"): each board candidate's board route, simulated over 32 draws of the
# parametric delay model (bench_gate.sh draw:K: chains and rest bands independent, uniform [0.20, 0.31]; CARRY4 / F7F8 /
# FF uniform [0.20, 1.0]; setting M scatter seeded by K), the fixed verdict (runs must agree). Result: the fraction of
# draws that return every right answer. Task = candidate x a block of 8 draws:
#   c0 item 33 fxa s27 | c1 item 27 fxd s2 | c2 item 31 fcsel3a s20 | c3 item 28 fcsel3m s20 | c4 item 29 fisel3m s19 |
#   c5 item 30 fc64sel3 s10 | c6 item 32 fc64sel3p s22 | c7 CONTROL: fxd s2 with ucond_br6's condition late (SDF only),
#   draws 1-16 +3000 ps (steerneg: fails only at FAST_MIN, which no draw reaches; locally draw 1 PASS), draws 17-32 +8000
#   (steerneg: fails at FAST_MIN and worst). The draw model must fail the +8000 half.
set -uo pipefail
C=$(( (TASK-1) / 4 )); B=$(( (TASK-1) % 4 ))
G=research/data/eventgraph/gate
XENV="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0"
CENV="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
IENV="BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
case $C in
  0) N=fxa; K=xorshift; S=27; Z=research/data/xorshift_sizes_T3s50_fr4a_bench.vh; V=xor19; E=$XENV;;
  1|7) N=fxd; K=xorshift; S=2; Z=research/data/xorshift_sizes_T3s50_fr4_bench.vh; V=xor19; E=$XENV;;
  2) N=fcsel3a; K=collatz; S=20; Z=research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh; V=col14; E=$CENV;;
  3) N=fcsel3m; K=collatz; S=20; Z=research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh; V=col14; E=$CENV;;
  4) N=fisel3m; K=ipow; S=19; Z=research/data/ipow_dsp1_sizes_T9s75_h4s3m_bench.vh; V=ipow17; E=$IENV;;
  5) N=fc64sel3; K=collatz64; S=10; Z=research/data/collatz64_sizes_T4cdb_h4s3_bench.vh; V=c6415; E=$CENV;;
  6) N=fc64sel3p; K=collatz64; S=22; Z=research/data/collatz64_sizes_T4cdb_h4s3p_bench.vh; V=c6415; E=$CENV;;
esac
case $K in xorshift) export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir;;
           collatz|collatz64) export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/${K}_preeq2.mlir;; esac
NM=dr_${N}_$S
echo "candidate c$C $N kernel $K seed $S block $B vectors $V" > "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $S research/data/fifteen/vec_${K%64}.hex $G/$V.hex $G/$V.exp $E > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
md5sum "$HW/$D.sdf" "$RD/xray.sdf" >> "$OUT/task.txt"
SDF=$RD/xray.sdf
if [ $C = 7 ]; then
  python3 research/tools/fifteen/sdf_inject.py "$RD/xray.sdf" "$RUNS/inj.sdf" '^(?!.*_j\.u)' 'ucond_br6\.u\$LUT[56]/' $([ $B -lt 2 ] && echo 3000 || echo 8000) > "$OUT/inject.txt" 2>&1 || { echo "nothing injected" >> "$OUT/task.txt"; exit 1; }
  SDF=$RUNS/inj.sdf
fi
run() { k=$1; W=$RUNS/d/$k; mkdir -p "$W"; cp "$SDF" "$W/xray.sdf"
  r=$(timeout 100m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" draw:$k 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3- "$W/draw_$k.txt" 2>/dev/null) => ${r:-TIMEOUT/none}" > "$OUT/draw_$k.txt"
  grep '^BENCHRES' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$k.txt"; }
for w in 0 1; do
  for j in 1 2 3 4; do k=$(( B*8 + w*4 + j )); run $k & done; wait
done
cat "$OUT"/draw_*.txt >> "$OUT/task.txt"
