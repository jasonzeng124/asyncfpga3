#!/bin/bash
#CLUSTER array=1-32 cores=2 mem=16G time=240
# suite13t_s3a_rwa (set A of suite13t_s5b_sib, split off 2026-11-20 14:09 UTC so it runs before suite13t seeds 3-4): bdc BDC_SIBLING_FUSE=1 (0218b747f) through flow v9 + the trim step (suite13t's environment) with
# AUTO_TRIM_SCOPE=cycle, seeds 1-4, on two sets:
#   A (tasks 1-32): formal's proved loop-test passes (research/data/autorw/K.mlir, Lean-proved by structure: the plain
#      move on xorshift countloop twoloops quadrec horner varshift, eq2 on collatz collatz64) + BDC_SIBLING_FUSE=1 (the
#      plain move's parallel increment and test fused into one cell); and
#   B (tasks 33-116): 21 of the 23 default fixtures BDC_SIBLING_FUSE=1 changes, no rewrite (sobel / video_filter left
#      out: their loops do not fit 240 min).
# Named to run after suite13t (the headline) and its rerun.
# Control: suite13t's same (kernel, seed); compare P_untrimmed (the trim scope differs: cycle here, all there).
# PREDICTION (2026-11-20 12:55 UTC, before any result here or of the local loops): set A, P_untrimmed below suite13t's same
# seed by 5-15 % on the six plain-move kernels (the fused cell covers max(add, compare) instead of their sum) and by
# 10-25 % on collatz / collatz64 (eq2; the md5-keyed version gave -24 / -26 % before ring fusion); set B within route
# scatter overall (median -3 .. +3 %), some kernels worse (a merged cell makes a short branch wait for the longest
# one's line); every draw passes everywhere; rule-clean share as suite13t's.
set -uo pipefail
A=(xorshift countloop twoloops quadrec horner varshift collatz collatz64)
B=(ipow gcd isprime straight countloop sqrtsub twoloops horner varshift nested branchloop fill factorial iterative_division iterative_sqrt if_loop_1 if_convert test_flatten_array image_resize stencil_2d nested_loop)
if [ "$TASK" -le 32 ]; then K=${A[$(( (TASK - 1) % 8 ))]}; S=$(( (TASK - 1) / 8 + 1 )); export MLIR_OVERRIDE=research/data/autorw/$K.mlir; SET=A
else T2=$((TASK - 33)); K=${B[$(( T2 % 21 ))]}; S=$(( T2 / 21 + 1 )); SET=B; fi
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle BDC_SIBLING_FUSE=1
echo "suite13t_s3a_rwa set $SET kernel $K seed $S ${MLIR_OVERRIDE:+(MLIR_OVERRIDE=$MLIR_OVERRIDE)}" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
rm -f "$OUT/auto/"place_*.txt
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
