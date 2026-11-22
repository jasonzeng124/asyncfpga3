#!/bin/bash
#CLUSTER array=5,6,10,14,18,19,20,21,22,24,31 cores=4 mem=32G time=240
# AUTO_CKPT=1 added 2026-11-22 before this part was submitted (research/JOURNAL.md 2026-11-22): final()'s full stacks
# and trim-step rule runs and the draws are memoized by content in the task's auto/ files, so a resume (from $SHARED)
# no longer redoes them; results are unchanged by construction (a memo is keyed by every input its run reads).
# Memo files stay out of OUT/auto.
# suite13t_s5a_v12_1a_r1: resumes suite13t_s5a_v12_1a's 11 task(s) that ended without a result line (5,6,10,14,18,19,20,21,22,24,31), from their $SHARED state; the same
# body otherwise (same kernel / seed per task number), 4 cores with the four draws at once.
# suite13t_s5a_v12_1a: seed 1, kernels 1-31 of KS
# flow v12 = flow v11 + two opt-in knobs, both general (no kernel named), each measured first (research/JOURNAL.md 2026-11-21):
#   * AUTO_LATE_AFTER_SEARCH=1: v11's late overbuild phase only after the SEARCH phase has failed too. v11 ran it
#     before the search and skipped the search for its route, which cost the kernels v10's search rescued (seed 1:
#     countloop 19.12 -> 23.17 ns, memsum 24.56 -> 28.19, dot2 27.43 -> 29.26). Local test: countloop s1 ships v10's
#     search route again; cmpchain s1 (nothing to search) re-enters into v11's late route (the same sdf).
#   * AUTO_GUARD_E=0.90,1.10: rule E / J's guard at 10 % instead of 3 %, so every select gate tolerates a path error of
#     x = 0.10 by the rule's own arrivals. Why: formal B30 -- three rule-CLEAN v10 routes (collatz64, sqrtsub, lfsrfind
#     s1) fail its race-only adversary at kappa 0.06-0.10; their guarded rebuilds do not (none / none / kappa 0.15). Cost:
#     static +0.5 % P over all 46 suite routes; the farm's paired test suite13t_s5g_g10: P ratio 1.003 over the 18 pairs
#     clean in both, but two seeds lost convergence (sqrtsub s2 shipped NOT CLEAN, a draw failed) -- which the late
#     phase is there to absorb -- local test under this exact environment: sqrtsub s2 rule-CLEAN after the late
#     phase, PASS 4 / 4 (draw 10204, which failed the guard-alone route, passes), at P 27.33 ns vs v10's 21.66.
# Control: flow v11's and v10's same (kernel, seed). PREDICTION (before any task): no kernel worse than v11's status;
# P no worse than v10's on the kernels v10's search rescued; every shipped route's weakest select gate at x >= 0.10.
set -uo pipefail
KS=(xorshift collatz collatz64 ipow gcd isprime straight countloop sqrtsub nest3 twoloops brhash lfsrfind quadrec horner fold64 varshift cmpchain nested branchloop digitsum digitdiv divmodu divmods test_divui memsum dot2 gather fill factorial iterative_division iterative_sqrt test_loop_free test_int16 test_bitint unused_arg if_loop_1 if_loop_2 sumi3_mem fir simple_example_1 while_loop_3 if_convert test_memory_1 test_memory_2 test_bool_array binary_search mul_example share_test_2 test_stdint spmv sobel test_flatten_array image_resize vector_rescale stencil_2d iir share_test_1 single_loop loop_path nested_loop video_filter)
NK=${#KS[@]}
K=${KS[$(( TASK - 1 + 0 ))]}; S=1
export CA_JOBS=2 DRAW_JOBS=4 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle AUTO_RACE_Z=4.5 AUTO_PROVED_RW=cache AUTO_OVERBUILD=3 AUTO_OVERBUILD_LATE=4 TRIM_STAGEFIX=1 AUTO_RACE_KEEP=1 AUTO_PROVED_RW_CACHE=research/data/autorw/cache_v11.tsv AUTO_LATE_AFTER_SEARCH=1 AUTO_GUARD_E=0.90,1.10 AUTO_CKPT=1
echo "suite13t_s5a_v12 kernel $K seed $S (flow v12)" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
# $SHARED state (added 2026-11-20 15:45 UTC, before this request started; the flow is unchanged): suite13t lost ~30 % of
# its tasks to the 240-min limit (13 kernels on every seed so far), most after their loop had shipped. This task's auto/
# files also go to $SHARED/state_v12/K_S every 5 min (non-empty files only, each by rename); a later request with this
# same body (a resume part, filed with the tasks that ran out of time) finds them and goes on: AUTO_RESUME (the loop from
# its last ratchet step, then the search phase and the final stacks again) or, when the loop had finished,
# AUTO_TRIM_ONLY (the shipped route rebuilt from its sizes, seed and structure, checked by sdf md5, trimmed and timed
# again), then the draws. The trim records are dropped first (it_I.txt gets the untrimmed line back: same route, same
# sdf). A task that ends with a result line removes its state.
ST=$SHARED/state_v12/${K}_$S
if [ -f "$ST/sizes_1.vh" ]; then
  mkdir -p "$RUNS/state" && cp "$ST"/* "$RUNS/state/" 2>/dev/null
  for f in "$RUNS/state"/*; do b=${f##*/}
    case $b in it_*_untrimmed.txt) mv "$f" "$RUNS/state/${b%_untrimmed.txt}.txt";; trim_*|sizes_*_trim*|snap_*) rm -f "$f";; esac
  done
  export AUTO_RESUME=$RUNS/state; how="the loop goes on"
  if grep -qE '^(CLEAN|NOT CLEAN)' "$RUNS/state/result.txt" 2>/dev/null; then export AUTO_TRIM_ONLY=1; how="the loop had finished: trim-only"; fi
  echo "resumed from SHARED/state_v12/${K}_$S ($(ls "$RUNS/state" | wc -l) files; $how)" >> "$OUT/task.txt"
fi
mkdir -p "$ST"
save() { cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
  rm -f "$OUT/auto/"stk_*.txt "$OUT/auto/"rck_*.txt "$OUT/auto/"dck_*.txt
  local f; for f in "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh; do
    [ -s "$f" ] && cp "$f" "$ST/.part" 2>/dev/null && mv "$ST/.part" "$ST/${f##*/}"; done; }
( while sleep 300; do save; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null; wait $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
rm -f "$OUT/auto/"place_*.txt "$OUT/auto/"stk_*.txt "$OUT/auto/"rck_*.txt "$OUT/auto/"dck_*.txt
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
it=$(grep -oP 'it=\K[0-9]+' "$OUT/result.txt" 2>/dev/null | head -1)
for c in 0.20 0.31; do
  f=$RUNS/ca/su_${K}_${S}_$it/rule_$c/soak.sdf
  [ -n "$it" ] && [ -f "$f" ] && python3 research/tools/caphold.py "$f" > "$OUT/caphold_$c.txt" 2>&1
done
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
if grep -q "status=" "$OUT/result.txt" 2>/dev/null; then rm -rf "$ST"; else save; fi
exit 0
