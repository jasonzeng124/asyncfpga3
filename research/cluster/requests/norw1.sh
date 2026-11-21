#!/bin/bash
#CLUSTER array=1-24 cores=3 mem=16G time=240
# norw1: THE AUTOMATIC COLUMN WITHOUT A LIST OF KERNELS (owner, PROGRAM 2026-11-18, auditor T156): BDC_AUTO=1 with
# bdc/auto.py's md5-keyed MLIR rewrites OFF (the new default; BDC_AUTO_REWRITES=1 is the named variant "with the three
# rewrites" that suite6 ran). xorshift, collatz, collatz64 x seeds 1-8 -- the only kernels the rewrites ever matched;
# ipow, gcd, isprime and every suite kernel are unchanged by the switch (auto.py's output equals its input on all of
# build/frontend but those three, checked). Flow v6 otherwise (auto_size.sh: start x 0.3, two-corner rule, join credit,
# steer self-bound, token floor, finish phase; + the bench-clock seed fallback), 8 draws per route (suite6's draw
# points), expected values from the C. suite6 (same seeds, rewrites on) is the other column.
# PREDICTION (2026-11-18 19:49 UTC; from the hand recipes' rewrite levers: collatz item 25 vs 22 -5.4 ns, collatz64 -9.0
# ns paired on 31 seeds, xorshift lever 8 a few ns): medians xorshift ~24-26 ns (suite6 22.28), collatz ~20-22 (17.04),
# collatz64 ~28-32 (23.27); every judged route passes its draws.
set -uo pipefail
KS=(xorshift collatz collatz64)
K=${KS[$(( (TASK - 1) / 8 ))]}; S=$(( (TASK - 1) % 8 + 1 ))
export CA_JOBS=2 DRAW_JOBS=1 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0
echo "norw1 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 8 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
