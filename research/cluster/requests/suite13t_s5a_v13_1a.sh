#!/bin/bash
#CLUSTER array=1-31 cores=2 mem=16G time=240
# AUTO_CKPT=1 added 2026-11-22 before this part was submitted (research/JOURNAL.md 2026-11-22): final()'s full stacks
# and trim-step rule runs and the draws are memoized by content in the task's auto/ files, so a resume (from $SHARED)
# no longer redoes them; results are unchanged by construction (a memo is keyed by every input its run reads).
# Memo files stay out of OUT/auto.
# suite13t_s5a_v13_1a: seed 1, kernels 1-31 of KS
# flow v13 = flow v12 + three opt-in knobs, all general (no kernel named), each measured first (research/JOURNAL.md
# 2026-11-21 18:52 - 2026-11-22 00:02):
#   * AUTO_RACE_KAPPA=0.13: the latch-fed steer race checked at formal's split corners (research/tools/race_kappa.py:
#     request at each arc's corner minimum, condition at its maximum; = formal's ctl term, B37), its link padded below
#     0.13 (formal B32's separation: 9 of its 10 adversary failures inside 0.20 were at <= 0.125). Why: v10 sqrtsub s4
#     and v11 test_flatten_array s2 passed AUTO_RACE_Z=4.5 yet lose formal's race-only adversary at kappa 0.03 (B32 /
#     B36); 7 of the 19 adversary failures at <= 0.10 are this class (B38). Local: on both routes the check fires
#     (kappa 0.011 / 0.000 = formal's slacks) and the padded re-route is at 0.43 / 0.24; under v10's environment the
#     extra route cost sqrtsub s4 its convergence (NOT CLEAN), under v11's the late phase made test_flatten_array s2
#     clean one route later, PASS 4 / 4, at +11.6 % call latency (research/data/racek/README.md).
#   * BDC_MEM_FASTFALL=2: the memory port's setup / clock-to-out lines rise through their elements and fall in one
#     (bd_mem_ff), on every port -- =1 never reached the arbitrated host port (binary_search, mul_example,
#     test_bool_array, test_memory_1 / 2, test_stdint built byte-identical routes to v10's under it). The mff A/B
#     (v10 + =1, seeds 1-2): P ratio 0.953 over 12 clean pairs. Local =2 runs (the arbitrated port as bd_mem_ff, a
#     GLS first): test_stdint s1 / s2 PASS 4 / 4 (P 49.21 / 46.21 vs v10 53.27 / 47.89), mul_example s1 PASS 4 / 4
#     (55.77 vs 56.03), all rule-CLEAN, arrays right, no pulse under 1 ns.
#   * AUTO_TRIM_PORTS=1: the cycle-scoped trim also reaches a memory port's own lines (cycle_macros.py never mapped
#     them). Same-route tests on mff routes (research/data/trimports/): dot2 s2 -10.1 %, gather s2 -13.1 %, gather s1
#     -6.4 %, if_loop_2 s1 -14.4 % (P ratio 0.89 geomean), 16 / 16 draws PASS, rule-CLEAN; mul_example s2 (plain port)
#     unchanged.
# Control: flow v12's same (kernel, seed). PREDICTION (before any task): on non-memory kernels v13 ships v12's route
# except where a latch-fed race is below 0.13 (formal's census: about a third of the routes with such a race), with no
# kernel losing PASS; memory kernels' P lower than v12's on the geometric mean (the port is 42 % of their cycles,
# median); no draw fails.
set -uo pipefail
KS=(xorshift collatz collatz64 ipow gcd isprime straight countloop sqrtsub nest3 twoloops brhash lfsrfind quadrec horner fold64 varshift cmpchain nested branchloop digitsum digitdiv divmodu divmods test_divui memsum dot2 gather fill factorial iterative_division iterative_sqrt test_loop_free test_int16 test_bitint unused_arg if_loop_1 if_loop_2 sumi3_mem fir simple_example_1 while_loop_3 if_convert test_memory_1 test_memory_2 test_bool_array binary_search mul_example share_test_2 test_stdint spmv sobel test_flatten_array image_resize vector_rescale stencil_2d iir share_test_1 single_loop loop_path nested_loop video_filter)
NK=${#KS[@]}
K=${KS[$(( TASK - 1 + 0 ))]}; S=1
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle AUTO_RACE_Z=4.5 AUTO_PROVED_RW=cache AUTO_OVERBUILD=3 AUTO_OVERBUILD_LATE=4 TRIM_STAGEFIX=1 AUTO_RACE_KEEP=1 AUTO_PROVED_RW_CACHE=research/data/autorw/cache_v11.tsv AUTO_LATE_AFTER_SEARCH=1 AUTO_GUARD_E=0.90,1.10 AUTO_RACE_KAPPA=0.13 BDC_MEM_FASTFALL=2 AUTO_TRIM_PORTS=1 AUTO_CKPT=1
echo "suite13t_s5a_v13 kernel $K seed $S (flow v13)" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
# $SHARED state (added 2026-11-20 15:45 UTC, before this request started; the flow is unchanged): suite13t lost ~30 % of
# its tasks to the 240-min limit (13 kernels on every seed so far), most after their loop had shipped. This task's auto/
# files also go to $SHARED/state_v13/K_S every 5 min (non-empty files only, each by rename); a later request with this
# same body (a resume part, filed with the tasks that ran out of time) finds them and goes on: AUTO_RESUME (the loop from
# its last ratchet step, then the search phase and the final stacks again) or, when the loop had finished,
# AUTO_TRIM_ONLY (the shipped route rebuilt from its sizes, seed and structure, checked by sdf md5, trimmed and timed
# again), then the draws. The trim records are dropped first (it_I.txt gets the untrimmed line back: same route, same
# sdf). A task that ends with a result line removes its state.
ST=$SHARED/state_v13/${K}_$S
if [ -f "$ST/sizes_1.vh" ]; then
  mkdir -p "$RUNS/state" && cp "$ST"/* "$RUNS/state/" 2>/dev/null
  for f in "$RUNS/state"/*; do b=${f##*/}
    case $b in it_*_untrimmed.txt) mv "$f" "$RUNS/state/${b%_untrimmed.txt}.txt";; trim_*|sizes_*_trim*|snap_*) rm -f "$f";; esac
  done
  export AUTO_RESUME=$RUNS/state; how="the loop goes on"
  if grep -qE '^(CLEAN|NOT CLEAN)' "$RUNS/state/result.txt" 2>/dev/null; then export AUTO_TRIM_ONLY=1; how="the loop had finished: trim-only"; fi
  echo "resumed from SHARED/state_v13/${K}_$S ($(ls "$RUNS/state" | wc -l) files; $how)" >> "$OUT/task.txt"
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
