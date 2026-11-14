#!/usr/bin/env bash
# eval_task.sh NAME KERNEL SIZES_VH SEED VEC GATE_HEX GATE_EXP [ENV...] -- one route, every check, for the farm
# (research/cluster/README.md) or locally.  Writes a summary to ${OUT:-.}/eval.txt:
#   1. the bench build + itercost stack + event graph (lane2.sh; MLIR_OVERRIDE honoured): period, odata, fasm_equiv, ffmux
#   2. the static check of the owner's full-range rule (JOURNAL 2026-11-14): corner_audit at NOMINAL (--uniform 0.288)
#      and WORST, measured-residual guards, on this route as built; every kernel rule A / A' / E constraint below 0
#      (tighten's unsized bundled-channel row "a" is listed apart)
#   3. the full gate: bench_gate.sh SLOW_MAX / FAST_MIN / worst+M with the C-derived oracle.
#   4. (HOLD_VEC=vector file) the trace-measured hold check at FAST_MIN (hold_trace.py) -> hold.tsv.
# Steps 2 and 3 run in parallel (5 processes; memory ~3 x 2.4 GB for the gate sims).
set -uo pipefail
N=$1; K=$2; Z=$3; S=$4; VEC=$5; GH=$6; GE=$7; shift 7
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/home/user/runs}; export RUNS
O=${OUT:-$PWD}; mkdir -p "$O"; E=$O/eval.txt; : > "$E"
L=$R/research/tools/fifteen/lane2.sh
line=$("$L" "e$S" "$N" "$K" "$Z" "$S" "$VEC" "$@" 2>&1 | tail -1)
echo "build $line" >> "$E"
HW=$RUNS/hw/$N; RD=$RUNS/r/$N
[ -f "$HW/${K}_bench_gen.sdf" ] || { echo "RESULT build-failed" >> "$E"; tail -20 "$HW/build.log" > "$O/build_tail.txt" 2>/dev/null; exit 1; }
CA=$RUNS/ca/$N; mkdir -p "$CA/seed1/pnr"
ln -sf "$RD/xray.sdf" "$CA/seed1/pnr/soak_xray.sdf"; ln -sf "$HW/${K}_bench_gen_routed.json" "$CA/seed1/pnr/soak_routed.json"
cp "$R/$Z" "$CA/seed1/pnr/sizes.vh"
cp "$R/${MLIR_OVERRIDE:-build/frontend/$K/comp/handshake_transformed.mlir}" "$CA/input.mlir"
python3 "$R/research/tools/corner_audit.py" "$CA/seed1" --prefix bridge_i.udut. --out "$CA/worst" > "$CA/worst.log" 2>&1 &
python3 "$R/research/tools/corner_audit.py" "$CA/seed1" --prefix bridge_i.udut. --uniform 0.288 --out "$CA/nom" > "$CA/nom.log" 2>&1 &
G=$RUNS/g/$N
for C in max min worst; do
  ( r=$("$R/research/tools/eventgraph/bench_gate.sh" "$HW" "${K}_bench_gen" "$G/$C" "$R/$GH" "$R/$GE" "$C" 2>&1 | tail -1)
    echo "gate $C $r" > "$O/gate_$C.txt" ) &
done
if [ -n "${HOLD_VEC:-}" ]; then   # trace-measured hold at every link / pipe input stage, FAST_MIN (hold_trace.py)
  ( DUMP_FIELD=min "$R/research/tools/eventgraph/fullstack_dump.sh" "$HW" "${K}_bench_gen" "$RUNS/hold/$N" "$R/$HOLD_VEC" > "$RUNS/hold_$N.log" 2>&1
    python3 "$R/research/tools/fifteen/hold_trace.py" "$RUNS/hold/$N" "$HW/${K}_kernel_bench.v" > "$O/hold.tsv" 2>&1
    rm -f "$RUNS/hold/$N/dump.vcd" ) &
fi
wait
for c in nom worst; do
  f=$CA/$c/report.txt
  if [ -f "$f" ]; then
    neg=$(awk '$1~/^(A|E)$/ && $2+0<0 && $3~/udut/ {print $1, $2, $3}' "$f" | sort -u | sed 's/bridge_i.udut.//' | tr '\n' ';')
    a=$(awk '$1=="a" && $2+0<0 && $3~/udut/ {print $2, $3}' "$f" | sort -u | sed 's/bridge_i.udut.//' | tr '\n' ';')
    echo "static $c ${neg:-CLEAN} | tighten-a: ${a:-none}" >> "$E"
    sed -n '/^proposal/,/^wrote/p' "$CA/$c.log" | head -40 > "$O/proposal_$c.txt"
  else echo "static $c ERROR (see ca_$c.log)" >> "$E"; tail -30 "$CA/$c.log" > "$O/ca_$c.log"; fi
done
cat "$O"/gate_*.txt >> "$E" 2>/dev/null
[ -f "$O/hold.tsv" ] && awk -F'\t' 'NR>1 && $6>0 {v=v $1"("$6"x,"$7"ps);"} NR==2 {m=$1" "$7} END {print "hold violations: " (v?v:"none") " | tightest " m}' "$O/hold.tsv" >> "$E"
cat "$E"
