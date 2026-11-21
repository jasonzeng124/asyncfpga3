#!/bin/bash
#CLUSTER array=1-14 cores=8 mem=32G time=180
# selneg: the select negative control on every kernel family, on each family's board-candidate route (PROGRAM "A check
# earns its place by failing"; collatz's by hand on fcsel0 s24, 2026-11-15, audit T118 CONFIRMED). Per task: one mux of
# one family; the route is built as on the board list, then +3000 ps is added in the prjxray SDF ONLY (same netlist and
# bits) to the select latch's output arcs into that mux's request joins (umuxN.uj0 / uj1; research/tools/fifteen/
# sdf_inject.py). Then: corner_audit on the injected SDF (rule E must flag it) and the full gate at FAST_MIN / worst /
# SLOW_MAX on it, each under a 50 min limit (a clean gate takes ~10; a hang is a failure by non-completion, the count of
# completed batches is kept). The clean route's static rows come from step 1 (eval_task STATIC_ONLY).
#   1-4 xorshift item 27 (seed 2, fr4, pre_dec) umux0-3     5-7 collatz64 item 26 (seed 25, h2, pre_eq2) umux0-2
#   8-11 ipow item 19 (seed 1, T9s75) umux0-3               12-14 collatz item 28 (seed 20, nl6s3m, pre_eq2) umux0-2
set -uo pipefail
R=$PWD
case $TASK in
  1|2|3|4) F=x27; K=xorshift; S=2; M=umux$((TASK-1)); Z=research/data/xorshift_sizes_T3s50_fr4_bench.vh
     export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir
     GH=research/data/eventgraph/gate/xor17.hex; GE=research/data/eventgraph/gate/xor17.exp; VEC=research/data/fifteen/vec_xorshift.hex
     ENVS="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0";;
  5|6|7) F=c64_26; K=collatz64; S=25; M=umux$((TASK-5)); Z=research/data/collatz64_sizes_T4cdb_h2_bench.vh
     export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir
     GH=research/data/eventgraph/gate/c6414.hex; GE=research/data/eventgraph/gate/c6414.exp; VEC=research/data/fifteen/vec_collatz.hex
     ENVS="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0";;
  8|9|10|11) F=ip19; K=ipow; S=1; M=umux$((TASK-8)); Z=research/data/ipow_dsp1_sizes_T9s75_bench.vh
     GH=research/data/eventgraph/gate/ipow17.hex; GE=research/data/eventgraph/gate/ipow17.exp; VEC=research/data/fifteen/vec_ipow.hex
     ENVS="BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0";;
  12|13|14) F=c28; K=collatz; S=20; M=umux$((TASK-12)); Z=research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh
     export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz_preeq2.mlir
     GH=research/data/eventgraph/gate/col13.hex; GE=research/data/eventgraph/gate/col13.exp; VEC=research/data/fifteen/vec_collatz.hex
     ENVS="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0";;
esac
N=selneg_${F}_$TASK
echo "family $F kernel $K seed $S mux $M" > "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $N $K $Z $S $VEC $GH $GE $ENVS > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$N; RD=$RUNS/r/$N; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
I=$RUNS/inj/$N; mkdir -p "$I"
python3 research/tools/fifteen/sdf_inject.py "$RD/xray.sdf" "$I/xray.sdf" '\.lat\.' "$M\.uj[01]/" 3000 > "$OUT/inject.txt" 2>&1 || { echo "nothing injected" >> "$OUT/task.txt"; exit 1; }
md5sum "$RD/xray.sdf" "$I/xray.sdf" >> "$OUT/task.txt"
CA=$RUNS/cainj/$N; mkdir -p "$CA/seed1/pnr"
ln -sf "$I/xray.sdf" "$CA/seed1/pnr/soak_xray.sdf"; ln -sf "$HW/${D}_routed.json" "$CA/seed1/pnr/soak_routed.json"
cp "$Z" "$CA/seed1/pnr/sizes.vh"; cp "${MLIR_OVERRIDE:-build/frontend/$K/comp/handshake_transformed.mlir}" "$CA/input.mlir"
python3 research/tools/corner_audit.py "$CA/seed1" --prefix bridge_i.udut. --out "$CA/worst" > "$CA/worst.log" 2>&1 &
python3 research/tools/corner_audit.py "$CA/seed1" --prefix bridge_i.udut. --uniform 0.288 --out "$CA/nom" > "$CA/nom.log" 2>&1 &
for C in min worst max; do
  ( W=$RUNS/gi/$N/$C; mkdir -p "$W"; cp "$I/xray.sdf" "$W/xray.sdf"
    r=$(timeout 50m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$GH" "$GE" "$C" 2>&1 | tail -1)
    nb=$(grep -c '^BENCHRES' "$W/$C/run.log" 2>/dev/null)
    echo "gate_inj $C ${r:-TIMEOUT/none} | BENCHRES lines $nb" > "$OUT/gate_inj_$C.txt"
    grep '^BENCHRES' "$W/$C/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_inj_$C.txt" ) &
done
wait
for m in worst nom; do
  cp "$CA/$m.log" "$OUT/ca_inj_$m.log" 2>/dev/null
  grep -E '^  [A-Z]+ +[-+]?[0-9]' "$CA/$m/report.txt" 2>/dev/null | sort -u > "$OUT/inj_rows_$m.txt"
  awk '$1=="E" && $2+0<0' "$OUT/inj_rows_$m.txt" | sed 's/bridge_i.udut.//' | awk '{print "inj static", m, $1, $2, $3, $4}' m=$m >> "$OUT/task.txt"
done
cat "$OUT"/gate_inj_*.txt >> "$OUT/task.txt"
