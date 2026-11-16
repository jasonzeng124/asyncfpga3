#!/bin/bash
#CLUSTER array=1-132 cores=8 mem=32G time=150
# zt1: the zero-trip input (n = 1, collatz(1) = 0) was missing from the collatz / collatz64 gate vectors (col13, c6414):
# the loop-ENTRY steers (ucond_br* fed by ucmpi0) never saw their condition change, so the gate could not judge rule E
# there (farm steerneg: +8000 ps into those steers passed every gate). col14 / c6415 = the old files with n = 1 as the
# second vector, oracle compiled from kernels/*.c (research/tools/fifteen/collatz_oracle.sh).
#   1-32 fcsel3a (BQ item 31 / section 32), 33-64 fcsel3m (item 28 / 29), 65-96 fc64sel3 (item 30 / 31),
#   97-128 fc64sel3p (item 32 / 33): build + static (STATIC_ONLY) + the gate with the new vectors at SLOW_MAX / FAST_MIN /
#   worst, default plusargs (as the board items were gated).
#   129-132: the board seeds of those four (fcsel3a 20, fcsel3m 20, fc64sel3 10, fc64sel3p 22): negative control, every
#   ucmpi0 -> entry-steer LUT arc +8000 ps (SDF only), gate FAST_MIN / worst with +META_INIT=0, on the new AND old vectors.
set -uo pipefail
R=$PWD
case $TASK in 129) T=20; F=0;; 130) T=20; F=1;; 131) T=10; F=2;; 132) T=22; F=3;; *) T=$(( (TASK-1) % 32 + 1 )); F=$(( (TASK-1) / 32 ));; esac
case $F in
  0) N=fcsel3a; K=collatz; Z=research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh;;
  1) N=fcsel3m; K=collatz; Z=research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh;;
  2) N=fc64sel3; K=collatz64; Z=research/data/collatz64_sizes_T4cdb_h4s3_bench.vh;;
  3) N=fc64sel3p; K=collatz64; Z=research/data/collatz64_sizes_T4cdb_h4s3p_bench.vh;;
esac
G=research/data/eventgraph/gate
if [ $K = collatz ]; then GN=$G/col14; GO=$G/col13; else GN=$G/c6415; GO=$G/c6414; fi
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/${K}_preeq2.mlir
NM=zt_${N}_$T
echo "family $N kernel $K seed $T task $TASK" > "$OUT/task.txt"
STATIC_ONLY=1 research/tools/fifteen/eval_task.sh $NM $K $Z $T research/data/fifteen/vec_collatz.hex $GN.hex $GN.exp \
  BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
HW=$RUNS/hw/$NM; RD=$RUNS/r/$NM; D=${K}_bench_gen
[ -f "$RD/xray.sdf" ] || { echo "no xray.sdf" >> "$OUT/task.txt"; exit 1; }
md5sum "$HW/$D.sdf" "$RD/xray.sdf" >> "$OUT/task.txt"
if [ $TASK -le 128 ]; then
  for C in max min worst; do
    ( W=$RUNS/g/$NM/$C; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
      r=$(timeout 120m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$GN.hex" "$GN.exp" "$C" 2>&1 | tail -1)
      echo "gate_zt $C ${r:-TIMEOUT/none}" > "$OUT/gate_$C.txt"
      grep '^BENCHRES' "$W/$C/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_$C.txt" ) &
  done
  wait; cat "$OUT"/gate_*.txt >> "$OUT/task.txt"; exit 0
fi
export GATE_PLUSARGS="+META_INIT=0"
I=$RUNS/inj/$NM; mkdir -p "$I"
python3 research/tools/fifteen/sdf_inject.py "$RD/xray.sdf" "$I/xray.sdf" 'ucmpi0\.' 'ucond_br[0-9]+\.u\$LUT[56]/' 8000 > "$OUT/inject.txt" 2>&1 || { echo "nothing injected" >> "$OUT/task.txt"; exit 1; }
for V in new old; do
  [ $V = new ] && GV=$GN || GV=$GO
  for C in min worst; do
    ( W=$RUNS/gi/$NM/$V/$C; mkdir -p "$W"; cp "$I/xray.sdf" "$W/xray.sdf"
      r=$(timeout 60m research/tools/eventgraph/bench_gate.sh "$HW" "$D" "$W" "$GV.hex" "$GV.exp" "$C" 2>&1 | tail -1)
      echo "gate_inj8000 vec_$V $C ${r:-TIMEOUT/none}" > "$OUT/gate_inj_${V}_$C.txt"
      grep '^BENCHRES' "$W/$C/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$OUT/benchres_inj_${V}_$C.txt" ) &
  done
done
wait; cat "$OUT"/gate_inj_*.txt >> "$OUT/task.txt"
