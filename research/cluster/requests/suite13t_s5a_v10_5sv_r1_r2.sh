#!/bin/bash
#CLUSTER array=1,2,3,4,5,6,7,8 cores=4 mem=16G time=240
# suite13t_s5a_v10_5sv_r1_r2: resumes suite13t_s5a_v10_5sv_r1's 8 task(s) that ended without a result line (1,2,3,4,5,6,7,8), from their $SHARED state; the same
# body otherwise (same kernel / seed per task number), 4 cores with the four draws at once.
# suite13t_s5a_v10_5sv_r1: resumes suite13t_s5a_v10_5sv's 8 task(s) that ended without a result line (1,2,3,4,5,6,7,8), from their $SHARED state; the same
# body otherwise (same kernel / seed per task number), 4 cores with the four draws at once.
# suite13t_s5a_v10_5sv (2026-11-20 21:15 UTC; named to run after v10's eight parts): flow v10 exactly (the same body and environment as suite13t_s5a_v10_1a..4b) on the two suite kernels v10 left out, sobel and video_filter, seeds 1-4 (tasks 1-8: kernel = task parity, seed = (task + 1) / 2). Why: they were left out of suite13t and v10 because their loops and draws do not fit one 240-min task (suite10b-10d); v10 parts now keep their state in $SHARED and resume parts go on from it, so they can get rows like every other kernel. Same state directory convention ($SHARED/state_v10/K_S).
# flow v9 + the trim step (suite13t) with three changes, all general (no kernel named anywhere):
#   * AUTO_TRIM_SCOPE=cycle (formal B25): the trim step moves only the lines on the route's critical cycle, round by
#     round, a round that buys no period reverted (on suite13t 13 % of the trims were on the cycle);
#   * AUTO_RACE_Z=4.5 (formal B21 / B28): a route the rule calls clean is also checked for its latch-fed steer races in
#     the draw model (research/tools/race_find.py); a race below 4.5 sd pads its link and the loop builds again;
#   * AUTO_PROVED_RW=cache: formal's Lean-proved loop-test passes (plain_pass, eq2_pass), memoized over every default
#     fixture (research/data/autorw/cache.tsv; 8 kernels rewritten, 54 none), checked by md5 at use.
# Control: suite13t's same (kernel, seed). PREDICTION: in the journal entry that files these requests.
set -uo pipefail
KS=(sobel video_filter)
NK=${#KS[@]}
K=${KS[$(( (TASK - 1) % 2 ))]}; S=$(( (TASK - 1) / 2 + 1 ))
export CA_JOBS=2 DRAW_JOBS=4 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle AUTO_RACE_Z=4.5 AUTO_PROVED_RW=cache
echo "suite13t_s5a_v10 kernel $K seed $S (flow v10)" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
# $SHARED state (added 2026-11-20 15:45 UTC, before this request started; the flow is unchanged): suite13t lost ~30 % of
# its tasks to the 240-min limit (13 kernels on every seed so far), most after their loop had shipped. This task's auto/
# files also go to $SHARED/state_v10/K_S every 5 min (non-empty files only, each by rename); a later request with this
# same body (a resume part, filed with the tasks that ran out of time) finds them and goes on: AUTO_RESUME (the loop from
# its last ratchet step, then the search phase and the final stacks again) or, when the loop had finished,
# AUTO_TRIM_ONLY (the shipped route rebuilt from its sizes, seed and structure, checked by sdf md5, trimmed and timed
# again), then the draws. The trim records are dropped first (it_I.txt gets the untrimmed line back: same route, same
# sdf). A task that ends with a result line removes its state.
ST=$SHARED/state_v10/${K}_$S
if [ -f "$ST/sizes_1.vh" ]; then
  mkdir -p "$RUNS/state" && cp "$ST"/* "$RUNS/state/" 2>/dev/null
  for f in "$RUNS/state"/*; do b=${f##*/}
    case $b in it_*_untrimmed.txt) mv "$f" "$RUNS/state/${b%_untrimmed.txt}.txt";; trim_*|sizes_*_trim*|snap_*) rm -f "$f";; esac
  done
  export AUTO_RESUME=$RUNS/state; how="the loop goes on"
  if grep -qE '^(CLEAN|NOT CLEAN)' "$RUNS/state/result.txt" 2>/dev/null; then export AUTO_TRIM_ONLY=1; how="the loop had finished: trim-only"; fi
  echo "resumed from SHARED/state_v10/${K}_$S ($(ls "$RUNS/state" | wc -l) files; $how)" >> "$OUT/task.txt"
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
