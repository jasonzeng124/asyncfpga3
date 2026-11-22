#!/bin/bash
#CLUSTER array=1-32 cores=2 mem=16G time=240
# suite1: the compiler suite's one command (research/tools/suite/suite_one.sh) on four original kernels, seeds 1-8
# (gcd and isprime left out: their gate and period vectors take hours per draw in simulation -- farm gcddraw1 timed out
# on 42 of 64 tasks -- so they get smaller vector budgets first):
# BDC_AUTO=1, the flow's own sizing (auto_size.sh: estimates -> CA_SIZERULE with C-element joins on the route as built ->
# re-route; lines ever lengthened pinned; on while a clean route still shortens; ships the last clean route; MAXIT 4),
# the bits checked, 4 draws per route (K = 10000 + 100 S + j), period P, latency, kernel LUTs.  Nothing set per kernel.  PREDICTION (written before any AUTO route finished): every route that is EQUIVALENT passes 4 / 4 draws; P median
# xorshift 28 (25-31), collatz 26 (23-30), collatz64 36 (32-40), ipow 30 (26-34) ns (research/data/auto/README.md 3b);
set -uo pipefail
KS=(xorshift collatz collatz64 ipow)
K=${KS[$(( (TASK - 1) / 8 ))]}; S=$(( (TASK - 1) % 8 + 1 ))
export CA_JOBS=2 DRAW_JOBS=1 PNR_TIMEOUT=3600
echo "suite1 kernel $K seed $S" > "$OUT/task.txt"
( while sleep 600; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$OUT/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
kill $BG 2>/dev/null
exit 0
