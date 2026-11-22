#!/bin/bash
#CLUSTER array=1-24 cores=3 mem=16G time=240
# split1: BDC_SPLIT_SOURCES=1 (subagent graphsearch: one source + constant per reader of a shared source, so each
# literal folds into its fused region and no fork couples the readers across the loop body) through the WHOLE automatic
# flow -- BDC_AUTO=1 with no kernel list (rewrites off), flow v6's sizing loop, 8 draws -- on the three kernels whose
# critical cycle ran through a shared source: collatz, collatz64, ipow x seeds 1-8. Compare per seed with norw1
# (collatz, collatz64: the same flow without the split) and suite6 (ipow: the rewrites never touched it, so suite6 is
# its no-split column). graphsearch measured the split only at the farm routes' own sizes (collatz -7.6 %, ipow -8.4 %,
# collatz64 -6.3 %, 13 / 13 draws); this is the first time the loop sizes it.
# PREDICTION (2026-11-18 21:51 UTC): medians 5-8 % below the no-split column of the same flow (collatz ~1.2 ns, ipow
# ~1.7 ns, collatz64 ~1.5 ns below), every judged route passing its draws; some loops time out (resume round).
set -uo pipefail
KS=(collatz collatz64 ipow)
K=${KS[$(( (TASK - 1) / 8 ))]}; S=$(( (TASK - 1) % 8 + 1 ))
export CA_JOBS=2 DRAW_JOBS=1 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 BDC_SPLIT_SOURCES=1
echo "split1 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 8 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
