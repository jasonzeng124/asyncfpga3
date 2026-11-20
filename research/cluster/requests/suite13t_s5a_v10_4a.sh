#!/bin/bash
#CLUSTER array=1-30 cores=2 mem=16G time=240
# suite13t_s5a_v10_4a (flow v10; named to run after suite13t and its rerun, before suite13t_s5c_sibb): flow v10 on every suite kernel (sobel / video_filter left out, as in suite13t), seed 4, kernels 1-30 of KS:
# flow v9 + the trim step (suite13t) with three changes, all general (no kernel named anywhere):
#   * AUTO_TRIM_SCOPE=cycle (formal B25): the trim step moves only the lines on the route's critical cycle, round by
#     round, a round that buys no period reverted (on suite13t 13 % of the trims were on the cycle);
#   * AUTO_RACE_Z=4.5 (formal B21 / B28): a route the rule calls clean is also checked for its latch-fed steer races in
#     the draw model (research/tools/race_find.py); a race below 4.5 sd pads its link and the loop builds again;
#   * AUTO_PROVED_RW=cache: formal's Lean-proved loop-test passes (plain_pass, eq2_pass), memoized over every default
#     fixture (research/data/autorw/cache.tsv; 8 kernels rewritten, 54 none), checked by md5 at use.
# Control: suite13t's same (kernel, seed). PREDICTION: in the journal entry that files these requests.
set -uo pipefail
KS=(xorshift collatz collatz64 ipow gcd isprime straight countloop sqrtsub nest3 twoloops brhash lfsrfind quadrec horner fold64 varshift cmpchain nested branchloop digitsum digitdiv divmodu divmods test_divui memsum dot2 gather fill factorial iterative_division iterative_sqrt test_loop_free test_int16 test_bitint unused_arg if_loop_1 if_loop_2 sumi3_mem fir simple_example_1 while_loop_3 if_convert test_memory_1 test_memory_2 test_bool_array binary_search mul_example share_test_2 test_stdint spmv test_flatten_array image_resize vector_rescale stencil_2d iir share_test_1 single_loop loop_path nested_loop)
NK=${#KS[@]}
K=${KS[$(( TASK - 1 + 0 ))]}; S=4
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle AUTO_RACE_Z=4.5 AUTO_PROVED_RW=cache
echo "suite13t_s5a_v10 kernel $K seed $S (flow v10)" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
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
exit 0
