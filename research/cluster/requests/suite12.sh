#!/bin/bash
#CLUSTER array=1-62 cores=2 mem=16G time=240
# suite12: every kernel research/tools/suite/kernels.txt lists, seed 1, through flow v8 -- BDC_AUTO=1 with no kernel list
# and its defaults at this commit: ring fusion (BDC_RING_FUSE=2, new in v8), the event-graph search phase, CA_FAST, the
# bench-clock seed fallback, rule B's RAM guard, the N-way mux select rule, rule A's peers confined to the cell, a finish
# budget of 6 routes shipping the least-short route; 4 draws with the runt monitor reporting; expected values from the C.
# The first whole-suite run of v8: compare per kernel with the headline's v7 / v6 routes (research/data/fifteen/README.md).
# PREDICTION (17:07 UTC): every kernel that passed under v7 passes; xorshift / collatz faster (ringfuse1: -1.9 / -1.2
# ns median), the rest within route scatter; fewer NOT CLEAN routes than v7 (the finish budget of 6); some divider /
# memory loops run out of time (resume round).
set -uo pipefail
KS=(xorshift collatz collatz64 ipow gcd isprime straight countloop sqrtsub nest3 twoloops brhash lfsrfind quadrec horner fold64 varshift cmpchain nested branchloop digitsum digitdiv divmodu divmods test_divui memsum dot2 gather fill factorial iterative_division iterative_sqrt test_loop_free test_int16 test_bitint unused_arg if_loop_1 if_loop_2 sumi3_mem fir simple_example_1 while_loop_3 if_convert test_memory_1 test_memory_2 test_bool_array binary_search mul_example share_test_2 test_stdint spmv sobel test_flatten_array image_resize vector_rescale stencil_2d iir share_test_1 single_loop loop_path nested_loop video_filter )
K=${KS[$((TASK - 1))]}; S=1
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0
echo "suite12 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
