#!/bin/bash
#CLUSTER array=1-54 cores=2 mem=16G time=240
# suite11: seeds 3-4 (suite10b ran 1-2) of the suite's one command on the 27 listed kernels that have never been through the automatic path (division /
# modulo: digitsum, digitdiv, divmodu, divmods, test_divui; Dynamatic's tests added by dyntests: stores, a load first,
# two loads, void kernels), seeds 1-2, and the 10 loops of suite9 that sent back no state to resume (nest3 s1-4,
# nested s1, iterative_sqrt s2, fill s1, fold64 s1, iterative_division s1, quadrec s3), from scratch. The flow as of this
# commit: BDC_AUTO=1 with no kernel list, auto_size.sh flow v6 + CA_FAST (identical proposals, 8-10x faster rule steps),
# rule B's RAM guard 400 ps, the bench-clock seed fallback; 4 draws, three at a time, with the runt monitor reporting
# (GATE_RUNTS=1) and the gate's x / RAMB18 checks; expected values from the C (memory kernels: every array read back).
# The state is copied back every 5 min (a resume round finishes what runs out of time).
# PREDICTION (15:42 UTC): as suite10b on seeds 1-2 -- most loops finish (the divider kernels slowly), every judged route
# passes its draws (the divider sized by the cell-confined rule A since 1daa7efd4); the flow is v7 with every default of
# this commit (the N-way mux rule, the RAM guard, CA_FAST, the seed fallback).
set -uo pipefail
NEW=(digitsum digitdiv divmodu divmods test_divui simple_example_1 while_loop_3 if_convert test_memory_1 test_memory_2
     test_bool_array binary_search mul_example share_test_2 test_stdint spmv sobel test_flatten_array image_resize
     vector_rescale stencil_2d iir share_test_1 single_loop loop_path nested_loop video_filter)
OLD=(nest3_1 nest3_2 nest3_3 nest3_4 nested_1 iterative_sqrt_2 fill_1 fold64_1 iterative_division_1 quadrec_3)
K=${NEW[$(( (TASK - 1) / 2 ))]}; S=$(( (TASK - 1) % 2 + 3 ))
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0
echo "suite11 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
