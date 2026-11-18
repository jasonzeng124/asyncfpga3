#!/bin/bash
#CLUSTER array=1-24 cores=2 mem=16G time=240
# suite8: the suite's one command on the kernels added 2026-11-18 (suitew; memsum): memory (memsum, dot2, gather,
# test_bitint, if_loop_1, if_loop_2, sumi3_mem, fir) and Dynamatic's scalar tests (test_loop_free, factorial,
# iterative_division, iterative_sqrt), seeds 1-2, the flow as of this commit (v6 + corner_audit sizing the memory lines,
# nextpnr 6e5d224472232d5d), 4 draws per route; memory kernels judged with GATE_MEMEXP (every array read back).
# PREDICTION: dot2, test_bitint, test_loop_free pass (as in suitew's smoke); gather now passes (its bd_mem lines are
# sized by the rule); the rest unknown; fir / sumi3_mem may run long (1000-element fills per call).
set -uo pipefail
KS=(memsum dot2 gather test_bitint if_loop_1 if_loop_2 sumi3_mem fir test_loop_free factorial iterative_division iterative_sqrt)
K=${KS[$(( (TASK - 1) / 2 ))]}; S=$(( (TASK - 1) % 2 + 1 ))
export CA_JOBS=2 DRAW_JOBS=1 PNR_TIMEOUT=3600
echo "suite8 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 600; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
