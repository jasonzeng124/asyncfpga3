#!/bin/bash
#CLUSTER array=1-34 cores=2 mem=16G time=240
# suite13t_s5c_sibb (rewritten 2026-11-20 20:55 UTC before it ran; was set B of suite13t_s5b_sib on flow v9, 84 tasks): flow
# v10 exactly (suite13t_s5a_v10_*'s environment) plus bdc BDC_SIBLING_FUSE=1 (0218b747f: a fork whose outputs all feed
# fusable ops in two or more regions becomes ONE multi-result cell), on the 17 default fixtures the flag changes that
# carry no proved rewrite (countloop, twoloops, horner, varshift left out: under v10 they get the plain move, and
# v10 + the flag there is suite13t_s3a_rwa), seeds 1 and 2. Control: v10's same (kernel, seed).
# Why rewritten: v10 is the flow the next headline comes from, so the pair should differ in this one flag; two seeds
# x 17 kernels (34 routes) are enough to see the sign of the effect, and the farm's time goes to flow v11 next.
# PREDICTION (2026-11-20 12:55 UTC, kept): within route scatter overall (median -3 .. +3 %), some kernels worse (formal
# A30: a merged cell makes every part wait for every input of the cell; on gcd the test waits on k, on factorial on
# acc, on ipow b * b waits on r); every draw passes everywhere; rule-clean share as v10's.
set -uo pipefail
B=(ipow gcd isprime straight sqrtsub nested branchloop fill factorial iterative_division iterative_sqrt if_loop_1 if_convert test_flatten_array image_resize stencil_2d nested_loop)
K=${B[$(( (TASK - 1) % 17 ))]}; S=$(( (TASK - 1) / 17 + 1 ))
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle AUTO_RACE_Z=4.5 AUTO_PROVED_RW=cache BDC_SIBLING_FUSE=1
echo "suite13t_s5c_sibb kernel $K seed $S (flow v10 + BDC_SIBLING_FUSE=1)" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
# $SHARED state (added 2026-11-20 15:45 UTC, before this request started; the flow is unchanged): suite13t lost ~30 % of
# its tasks to the 240-min limit (13 kernels on every seed so far), most after their loop had shipped. This task's auto/
# files also go to $SHARED/state_sibb/K_S every 5 min (non-empty files only, each by rename); a later request with this
# same body (a resume part, filed with the tasks that ran out of time) finds them and goes on: AUTO_RESUME (the loop from
# its last ratchet step, then the search phase and the final stacks again) or, when the loop had finished,
# AUTO_TRIM_ONLY (the shipped route rebuilt from its sizes, seed and structure, checked by sdf md5, trimmed and timed
# again), then the draws. The trim records are dropped first (it_I.txt gets the untrimmed line back: same route, same
# sdf). A task that ends with a result line removes its state.
ST=$SHARED/state_sibb/${K}_$S
if [ -f "$ST/sizes_1.vh" ]; then
  mkdir -p "$RUNS/state" && cp "$ST"/* "$RUNS/state/" 2>/dev/null
  for f in "$RUNS/state"/*; do b=${f##*/}
    case $b in it_*_untrimmed.txt) mv "$f" "$RUNS/state/${b%_untrimmed.txt}.txt";; trim_*|sizes_*_trim*|snap_*) rm -f "$f";; esac
  done
  export AUTO_RESUME=$RUNS/state; how="the loop goes on"
  if grep -qE '^(CLEAN|NOT CLEAN)' "$RUNS/state/result.txt" 2>/dev/null; then export AUTO_TRIM_ONLY=1; how="the loop had finished: trim-only"; fi
  echo "resumed from SHARED/state_sibb/${K}_$S ($(ls "$RUNS/state" | wc -l) files; $how)" >> "$OUT/task.txt"
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
it=$(grep -oP 'it=\K[0-9]+' "$OUT/result.txt" 2>/dev/null | head -1)
for c in 0.20 0.31; do
  f=$RUNS/ca/su_${K}_${S}_$it/rule_$c/soak.sdf
  [ -n "$it" ] && [ -f "$f" ] && python3 research/tools/caphold.py "$f" > "$OUT/caphold_$c.txt" 2>&1
done
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
if grep -q "status=" "$OUT/result.txt" 2>/dev/null; then rm -rf "$ST"; else save; fi
exit 0
