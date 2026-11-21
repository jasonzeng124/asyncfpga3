#!/bin/bash
#CLUSTER array=1-31 cores=2 mem=16G time=240
# suite13t_s5a_v11_4a: seed 4, kernels 1-31 of KS
# flow v11 (2026-11-21 02:00 UTC; named to run after flow v10's parts and resumes, before the mff / sibb A/Bs): every
# suite kernel (62: v10's 60 + sobel / video_filter), seeds 1-4; flow v10 (v9 + scoped trim + AUTO_RACE_Z=4.5 + the
# proved loop-test rewrites) with, all general (no kernel named anywhere):
#   * AUTO_OVERBUILD=3 AUTO_OVERBUILD_LATE=4 (56740456cf): v10's finish phase unchanged; a loop still NOT CLEAN after it
#     gets up to 4 more routes built with BD_SYMTRIM (cells/rtl/bd_latch.v c0f2bab80: symmetric delay lines from LUT2s
#     that pass the chain, so the trim reaches every line), every sized line +3 except the latch-fed race links, clean
#     when the trim step alone makes it so, the shipped route trimmed back to max(rule need, size - 3) first (266be9d16).
#     Routed-GLS evidence for BD_SYMTRIM: journal 2026-11-21 01:02 (as built and trimmed 4 / 4; a trim below the rule's
#     need FAILS 0 / 7 with RAM timing events). Locally the first overbuilt route was rule-CLEAN as built on 6 of 6
#     loops and the late phase's first route on v10's own cmpchain s1 state (never clean in v10) was too;
#   * TRIM_STAGEFIX=1 (d8f163b4a): trim_lines.py names a multi-stage link's _SDELAY line right (v10's trim step missed
#     such trims: it changes which cycle lines the trim can shorten);
#   * AUTO_RACE_KEEP=1 (a72f4a551): no trim shortens a latch-fed steer race's request line;
#   * AUTO_PROVED_RW_CACHE=cache_v11.tsv (ca02b7189): + formal A34's translation-validated plain move on brhash, nested.
# Control: flow v10's same (kernel, seed). State in $SHARED/state_v11 (resume parts as in v10).
# PREDICTION (2026-11-21 02:00 UTC, before any result here): routes equal to v10's (same sdf) wherever v10's loop
# shipped clean from phase 1-2 and no _SDELAY trim or race-kept line differs; the loops v10 left NOT CLEAN reach a
# rule-CLEAN route in the late phase on >= 80 % of them; every draw passes; v10's 5-7 UNFINISHED kernels mostly PASS.
set -uo pipefail
KS=(xorshift collatz collatz64 ipow gcd isprime straight countloop sqrtsub nest3 twoloops brhash lfsrfind quadrec horner fold64 varshift cmpchain nested branchloop digitsum digitdiv divmodu divmods test_divui memsum dot2 gather fill factorial iterative_division iterative_sqrt test_loop_free test_int16 test_bitint unused_arg if_loop_1 if_loop_2 sumi3_mem fir simple_example_1 while_loop_3 if_convert test_memory_1 test_memory_2 test_bool_array binary_search mul_example share_test_2 test_stdint spmv sobel test_flatten_array image_resize vector_rescale stencil_2d iir share_test_1 single_loop loop_path nested_loop video_filter)
NK=${#KS[@]}
K=${KS[$(( TASK - 1 + 0 ))]}; S=4
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle AUTO_RACE_Z=4.5 AUTO_PROVED_RW=cache AUTO_OVERBUILD=3 AUTO_OVERBUILD_LATE=4 TRIM_STAGEFIX=1 AUTO_RACE_KEEP=1 AUTO_PROVED_RW_CACHE=research/data/autorw/cache_v11.tsv
echo "suite13t_s5a_v11 kernel $K seed $S (flow v11)" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
# $SHARED state (added 2026-11-20 15:45 UTC, before this request started; the flow is unchanged): suite13t lost ~30 % of
# its tasks to the 240-min limit (13 kernels on every seed so far), most after their loop had shipped. This task's auto/
# files also go to $SHARED/state_v11/K_S every 5 min (non-empty files only, each by rename); a later request with this
# same body (a resume part, filed with the tasks that ran out of time) finds them and goes on: AUTO_RESUME (the loop from
# its last ratchet step, then the search phase and the final stacks again) or, when the loop had finished,
# AUTO_TRIM_ONLY (the shipped route rebuilt from its sizes, seed and structure, checked by sdf md5, trimmed and timed
# again), then the draws. The trim records are dropped first (it_I.txt gets the untrimmed line back: same route, same
# sdf). A task that ends with a result line removes its state.
ST=$SHARED/state_v11/${K}_$S
if [ -f "$ST/sizes_1.vh" ]; then
  mkdir -p "$RUNS/state" && cp "$ST"/* "$RUNS/state/" 2>/dev/null
  for f in "$RUNS/state"/*; do b=${f##*/}
    case $b in it_*_untrimmed.txt) mv "$f" "$RUNS/state/${b%_untrimmed.txt}.txt";; trim_*|sizes_*_trim*|snap_*) rm -f "$f";; esac
  done
  export AUTO_RESUME=$RUNS/state; how="the loop goes on"
  if grep -qE '^(CLEAN|NOT CLEAN)' "$RUNS/state/result.txt" 2>/dev/null; then export AUTO_TRIM_ONLY=1; how="the loop had finished: trim-only"; fi
  echo "resumed from SHARED/state_v11/${K}_$S ($(ls "$RUNS/state" | wc -l) files; $how)" >> "$OUT/task.txt"
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
