#!/usr/bin/env bash
# spec_select_task.sh NAME KERNEL SIZES_VH SEED VEC INST [ENV...] -- build one route (lane2.sh) and report only the
# in-cell select race of a BDC_SPEC_INC cell (spec_select.py) at NOMINAL and WORST, in ${OUT:-.}/select.txt.
# For routes whose full check ran before the select row existed (eval_task.sh has it since 2026-11-15).
set -uo pipefail
N=$1; K=$2; Z=$3; S=$4; VEC=$5; I=$6; shift 6
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/home/user/runs}; export RUNS
O=${OUT:-$PWD}; mkdir -p "$O"; F=$O/select.txt; : > "$F"
line=$("$R/research/tools/fifteen/lane2.sh" "e$S" "$N" "$K" "$Z" "$S" "$VEC" "$@" 2>&1 | tail -1)
echo "build $line" >> "$F"
HW=$RUNS/hw/$N; RD=$RUNS/r/$N; C=$RUNS/sel/$N; mkdir -p "$C"
[ -f "$RD/xray.sdf" ] || { echo "RESULT build-failed" >> "$F"; cat "$F"; exit 1; }
J=$HW/${K}_bench_gen_routed.json
python3 "$R/research/tools/corner_sdf.py" "$RD/xray.sdf" "$J" "$C/nom.sdf" --band 0.288 > /dev/null
python3 "$R/research/tools/corner_sdf.py" "$RD/xray.sdf" "$J" "$C/worst.sdf" --band 0.288 \
    --cell CARRY4=1,SELMUX2_1=1,SLICE_FFX=1 --inst-rx '\.chain\.g\[\d+\]\.u$:0.21' > /dev/null
for m in nom worst; do
  echo "select $m $(python3 "$R/research/tools/fifteen/spec_select.py" "$C/$m.sdf" "bridge_i.udut.$I" 2>&1 | tail -2 | tr "\n" " ")" >> "$F"
done
cat "$F"
