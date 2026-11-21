#!/bin/bash
#CLUSTER array=1-32 cores=3 mem=16G time=240
# suite6: the HEADLINE run -- the suite's one command on the four fast original kernels, seeds 1-8, flow v5 (733987e1a):
# BDC_AUTO=1 (+ the token floor, db544ea9f); auto_size.sh from the estimates x 0.3; the rule (C-element joins, join
# credit CA_JOINAWARE, steer self-bound BD_SKEW_STEER_SELF) at the draw model's two worst vertices merged per line;
# pinning; a raise-only finish phase with one element of headroom; 8 draws per route (K = 10000 + 100 S + j).
# PREDICTION: every EQUIVALENT route passes 8 / 8; P median xorshift 17.5 (16-19.5; UCMPI1 ~10 instead of 17),
# collatz ~19, collatz64 ~24, ipow ~22.
set -uo pipefail
KS=(xorshift collatz collatz64 ipow)   # gcd / isprime: suite7 (8 cores)
K=${KS[$(( (TASK - 1) / 8 ))]}; S=$(( (TASK - 1) % 8 + 1 ))
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600
echo "suite6 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 600; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
ND=8; export AUTO_FINISH=3
case $K in gcd|isprime) ND=4; AUTO_FINISH=1;; esac   # their simulations are slow: keep the task under its 240 min
research/tools/suite/suite_one.sh "$K" "$S" $ND 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
