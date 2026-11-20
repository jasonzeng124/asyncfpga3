#!/bin/bash
#CLUSTER array=1-240 cores=2 mem=16G time=240
# suite13: flow v9 candidate on every kernel research/tools/suite/kernels.txt lists except sobel and video_filter (their
# loops and draws ran out of 240 min in suite10b / 10c / 10d), seeds 1-4: v8 (suite12's defaults) plus
#   * the rule H fix of 2026-11-19 (599c89e6b: a memory load's capture latch `ucap` is a latch, not a controller),
#   * CA_BENCHCAP=1 (research/data/benchcap/: out0's data checked against the bench's synchronised capture; it removed
#     the unfixable A' rows at the out0 mux of gcd / isprime / iterative_sqrt; only the draws were missing),
# (AUTO_PLACE_KEEP is NOT on: it fails to route on 3 of 4 kernels tried, research/data/placekeep/README.md.)
# PREDICTION (2026-11-20 00:58 UTC, before any result): every kernel that passed in suite12 / capfix1 passes every draw (share_test_2
# stays NOT-A-BOARD-ROUTE until the DSP decoder is extended); rule-clean routes rise from suite12's seed-1 share (21 of
# 35 when counted) to at least 60 % of judged routes, with no 'unfixable' row left on the capture kernels or on
# gcd / isprime / iterative_sqrt's out0 mux (their loops may still end NOT CLEAN on re-route churn); P on the kernels
# CA_BENCHCAP does not touch within route scatter of suite12; some divider / memory loops hit the 240-min limit.
set -uo pipefail
KS=(xorshift collatz collatz64 ipow gcd isprime straight countloop sqrtsub nest3 twoloops brhash lfsrfind quadrec horner fold64 varshift cmpchain nested branchloop digitsum digitdiv divmodu divmods test_divui memsum dot2 gather fill factorial iterative_division iterative_sqrt test_loop_free test_int16 test_bitint unused_arg if_loop_1 if_loop_2 sumi3_mem fir simple_example_1 while_loop_3 if_convert test_memory_1 test_memory_2 test_bool_array binary_search mul_example share_test_2 test_stdint spmv test_flatten_array image_resize vector_rescale stencil_2d iir share_test_1 single_loop loop_path nested_loop)
NK=${#KS[@]}
K=${KS[$(( (TASK - 1) % NK ))]}; S=$(( (TASK - 1) / NK + 1 ))
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1
echo "suite13 kernel $K seed $S" > "$OUT/task.txt"
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
