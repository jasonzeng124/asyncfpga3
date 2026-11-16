#!/bin/bash
#CLUSTER array=1-96 cores=8 mem=32G time=150
# regate1: the gate's verdict read only the LAST run's odata of each 2-run batch, so a batch whose first run returned a
# wrong value passed (bench_gate.sh fixed 2026-11-16: mism_st bit 0 now fails the batch; farm steerneg had 5 such runs
# judged PASS; locally a late entry condition left the result stream one call behind from batch 3 on, every batch's last
# run still right). Re-gate the current board families with the fixed verdict and keep every BENCHRES line:
#   1-32 fxa (item 33 / section 34), 33-64 fxd (item 27 / 28), 65-96 fisel3m (ipow item 29 / 30).
#   xorshift: xor17 (the old set) and xor19 (+ zero-trip calls after looping calls); ipow: ipow17. 3 corners each.
set -uo pipefail
T=$(( (TASK-1) % 32 + 1 )); F=$(( (TASK-1) / 32 ))
case $F in
  0) N=fxa; K=xorshift; Z=research/data/xorshift_sizes_T3s50_fr4a_bench.vh;;
  1) N=fxd; K=xorshift; Z=research/data/xorshift_sizes_T3s50_fr4_bench.vh;;
  2) N=fisel3m; K=ipow; Z=research/data/ipow_dsp1_sizes_T9s75_h4s3m_bench.vh;;
esac
G=research/data/eventgraph/gate
if [ $K = xorshift ]; then
  export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir; VS="xor17 xor19"; VEC=research/data/fifteen/vec_xorshift.hex
  ENVS="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0"
else
  VS="ipow17"; VEC=research/data/fifteen/vec_ipow.hex
  ENVS="BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
fi
NM=rg_${N}_$T
echo "family $N kernel $K seed $T task $TASK" > "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $T $VEC $G/${VS%% *}.hex $G/${VS%% *}.exp $ENVS > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
md5sum "$HW/$D.sdf" "$RD/xray.sdf" >> "$OUT/task.txt"
for V in $VS; do for C in max min worst; do
  ( W=$RUNS/g/$NM/$V/$C; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
    r=$(timeout 120m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$G/$V.hex" "$G/$V.exp" "$C" 2>&1 | tail -1)
    echo "gate $V $C ${r:-TIMEOUT/none}" > "$OUT/gate_${V}_$C.txt"
    grep '^BENCHRES' "$W/$C/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_${V}_$C.txt" ) &
done; done
wait; cat "$OUT"/gate_*.txt >> "$OUT/task.txt"
