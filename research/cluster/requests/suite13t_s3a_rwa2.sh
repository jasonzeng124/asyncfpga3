#!/bin/bash
#CLUSTER array=17-32 cores=2 mem=16G time=240
# SPLIT 2026-11-20 17:25 UTC (before either half started): tasks 17-32 here, 1-16 in suite13t_s3a_rwa (same body),
# because the runner kept placing 60-core v10 parts ahead of this 64-core request; 32 cores each fit sooner.
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
# CHANGE 2026-11-20 15:50 UTC, before this request started: AUTO_RACE_Z=4.5 added (formal B28's latch-fed race check,
# on in flow v10). With it this set A is exactly flow v10 + BDC_SIBLING_FUSE=1 on the eight proved kernels (v10 reads
# the same proved MLIRs through AUTO_PROVED_RW=cache), so suite13t_s5a_v10_*'s same (kernel, seed) is its paired
# control for the sibling cell; on collatz / collatz64 the flag changes nothing (formal A30: emit is byte-identical), so
# those 8 routes are v10's own, early. PREDICTION for the change (15:50): against v10's same kernel and seed, the six
# plain-move kernels within -10 .. +5 % (local seed 1: xorshift -0.4 %), collatz / collatz64 identical routes (sdf
# md5 equal); against suite13t, the 12:55 prediction above stands with the race check's cost (up to one element on a
# padded link) on top.
set -uo pipefail
A=(xorshift countloop twoloops quadrec horner varshift collatz collatz64)
B=(ipow gcd isprime straight countloop sqrtsub twoloops horner varshift nested branchloop fill factorial iterative_division iterative_sqrt if_loop_1 if_convert test_flatten_array image_resize stencil_2d nested_loop)
if [ "$TASK" -le 32 ]; then K=${A[$(( (TASK - 1) % 8 ))]}; S=$(( (TASK - 1) / 8 + 1 )); export MLIR_OVERRIDE=research/data/autorw/$K.mlir; SET=A
else T2=$((TASK - 33)); K=${B[$(( T2 % 21 ))]}; S=$(( T2 / 21 + 1 )); SET=B; fi
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle BDC_SIBLING_FUSE=1 AUTO_RACE_Z=4.5
echo "suite13t_s3a_rwa2 set $SET kernel $K seed $S ${MLIR_OVERRIDE:+(MLIR_OVERRIDE=$MLIR_OVERRIDE)}" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
# $SHARED state (added 2026-11-20 15:45 UTC, before this request started; the flow is unchanged): suite13t lost ~30 % of
# its tasks to the 240-min limit (13 kernels on every seed so far), most after their loop had shipped. This task's auto/
# files also go to $SHARED/state_rwa/K_S every 5 min (non-empty files only, each by rename); a later request with this
# same body (a resume part, filed with the tasks that ran out of time) finds them and goes on: AUTO_RESUME (the loop from
# its last ratchet step, then the search phase and the final stacks again) or, when the loop had finished,
# AUTO_TRIM_ONLY (the shipped route rebuilt from its sizes, seed and structure, checked by sdf md5, trimmed and timed
# again), then the draws. The trim records are dropped first (it_I.txt gets the untrimmed line back: same route, same
# sdf). A task that ends with a result line removes its state.
ST=$SHARED/state_rwa/${K}_$S
if [ -f "$ST/sizes_1.vh" ]; then
  mkdir -p "$RUNS/state" && cp "$ST"/* "$RUNS/state/" 2>/dev/null
  for f in "$RUNS/state"/*; do b=${f##*/}
    case $b in it_*_untrimmed.txt) mv "$f" "$RUNS/state/${b%_untrimmed.txt}.txt";; trim_*|sizes_*_trim*|snap_*) rm -f "$f";; esac
  done
  export AUTO_RESUME=$RUNS/state; how="the loop goes on"
  if grep -qE '^(CLEAN|NOT CLEAN)' "$RUNS/state/result.txt" 2>/dev/null; then export AUTO_TRIM_ONLY=1; how="the loop had finished: trim-only"; fi
  echo "resumed from SHARED/state_rwa/${K}_$S ($(ls "$RUNS/state" | wc -l) files; $how)" >> "$OUT/task.txt"
fi
mkdir -p "$ST"
save() { cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
  local f; for f in "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh; do
    [ -s "$f" ] && cp "$f" "$ST/.part" 2>/dev/null && mv "$ST/.part" "$ST/${f##*/}"; done; }
( while sleep 300; do save; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null; wait $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
rm -f "$OUT/auto/"place_*.txt
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
if grep -q "status=" "$OUT/result.txt" 2>/dev/null; then rm -rf "$ST"; else save; fi
exit 0
