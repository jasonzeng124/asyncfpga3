#!/bin/bash
#CLUSTER array=1-28 cores=2 mem=16G time=240
# suite13t_s5g_g10 (filed 2026-11-21 07:08 UTC, named to run after flow v11's parts): flow v10 exactly (the same export
# line, the same body) + AUTO_GUARD_E=0.90,1.10 -- rule E / J sized with the request x 0.90 against the select x 1.10
# instead of 0.97 / 1.03, i.e. every select gate tolerates a path error x = 0.10 by the rule's own arrivals (formal B24's
# "fine" threshold). Kernels: the seven thinnest of flow v10's suite routes by that measure (research/data/suite/board/
# screen_v10/census.md: x 0.045-0.062 by rule E; collatz64 / sqrtsub / lfsrfind thin in formal's simulation too),
# seeds 1-4 each (task = kernel index + 7 x (seed - 1)). Nothing set per kernel; $SHARED state_g10 for resumes.
# Control: flow v10's same (kernel, seed) -- suite13t_s5a_v10_* and its resume parts.
# PREDICTION (written before any task ran): status no worse than v10's on any (kernel, seed); P on the routes clean in
# both within +5 % of v10's (median of the pairs; research/data/guardx/: the rule adds ~2 elements on a loop test, and
# the local collatz64 s1 run shipped 21.97 ns vs v10's 21.53); every shipped route's weakest select gate at x >= 0.10
# by research/tools/steer_tol.py (checked on local rebuilds of the shipped routes).
set -uo pipefail
KS=(collatz64 sqrtsub lfsrfind fill twoloops dot2 if_loop_2)
NK=${#KS[@]}
K=${KS[$(( (TASK - 1) % 7 ))]}; S=$(( (TASK - 1) / 7 + 1 ))
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle AUTO_RACE_Z=4.5 AUTO_PROVED_RW=cache AUTO_GUARD_E=0.90,1.10
echo "suite13t_s5g_g10 kernel $K seed $S (flow v10 + AUTO_GUARD_E=0.90,1.10)" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
# $SHARED state (added 2026-11-20 15:45 UTC, before this request started; the flow is unchanged): suite13t lost ~30 % of
# its tasks to the 240-min limit (13 kernels on every seed so far), most after their loop had shipped. This task's auto/
# files also go to $SHARED/state_g10/K_S every 5 min (non-empty files only, each by rename); a later request with this
# same body (a resume part, filed with the tasks that ran out of time) finds them and goes on: AUTO_RESUME (the loop from
# its last ratchet step, then the search phase and the final stacks again) or, when the loop had finished,
# AUTO_TRIM_ONLY (the shipped route rebuilt from its sizes, seed and structure, checked by sdf md5, trimmed and timed
# again), then the draws. The trim records are dropped first (it_I.txt gets the untrimmed line back: same route, same
# sdf). A task that ends with a result line removes its state.
ST=$SHARED/state_g10/${K}_$S
if [ -f "$ST/sizes_1.vh" ]; then
  mkdir -p "$RUNS/state" && cp "$ST"/* "$RUNS/state/" 2>/dev/null
  for f in "$RUNS/state"/*; do b=${f##*/}
    case $b in it_*_untrimmed.txt) mv "$f" "$RUNS/state/${b%_untrimmed.txt}.txt";; trim_*|sizes_*_trim*|snap_*) rm -f "$f";; esac
  done
  export AUTO_RESUME=$RUNS/state; how="the loop goes on"
  if grep -qE '^(CLEAN|NOT CLEAN)' "$RUNS/state/result.txt" 2>/dev/null; then export AUTO_TRIM_ONLY=1; how="the loop had finished: trim-only"; fi
  echo "resumed from SHARED/state_g10/${K}_$S ($(ls "$RUNS/state" | wc -l) files; $how)" >> "$OUT/task.txt"
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
