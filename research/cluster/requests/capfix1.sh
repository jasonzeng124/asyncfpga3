#!/bin/bash
#CLUSTER array=1-48 cores=2 mem=16G time=240
# capfix1: the 12 suite kernels with a memory-load CAPTURE station that have finished routes (bdc/mem.py CAPTURE,
# `bd_latch ucap`), seeds 1-4, flow v8 as suite12 ran it, with ONE change: cells/verify/tighten.py's RE_BD_LATCH now
# recognises `ucap` as a bd_latch (2026-11-19). Before, rule H read every capture LUT as a controller and reported
# 100-625 ps 'unfixable' hold rows between unrelated paths (37 071 rows on the farm's routes; the only short rows on 23
# of 49 shipped routes). The capture's real hold race is measured by research/tools/caphold.py instead (>= 17.6 ns on
# test_bool_array s1 it 6). sobel and video_filter (captures too) are left out: their loops and draws ran out of 240
# min twice (suite10c / suite10d); they need their own request.
# PREDICTION (2026-11-19 23:10 UTC), from suite12's seed-1 loop files with the ucap rows removed (the fix leaves every
# proposal unchanged -- the rows were unfixable -- so seed 1 rebuilds suite12's routes and only the stop / ship decision
# moves): seed 1 ships a rule-CLEAN route on every kernel whose suite12 loop finished: test_bool_array it 6 (suite12
# shipped it 1, 3 real short rows), mul_example it 5 (it 4, 1 row), test_memory_2 it 9 (it 4, 2 rows), vector_rescale
# it 7 (it 5, 2 rows), test_stdint it 4 and test_memory_1 it 10 (the same routes, now clean), share_test_2 it 6
# (still NOT-A-BOARD-ROUTE: fasm2net's DSP48E1 cascade gap); every draw still passes; seeds 2-4: most loops clean,
# and wall time per loop shorter than suite12's (a clean route ends the finish phase).
set -uo pipefail
KS=(test_memory_1 test_memory_2 test_bool_array binary_search mul_example share_test_2 test_stdint spmv image_resize
    vector_rescale iir share_test_1)
K=${KS[$(( (TASK - 1) % 12 ))]}; S=$(( (TASK - 1) / 12 + 1 ))
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0
echo "capfix1 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
# the capture's hold, measured on the shipped route at both rule corners (the route's rule dirs hold the corner SDFs)
it=$(grep -oP 'it=\K[0-9]+' "$OUT/result.txt" 2>/dev/null | head -1)
for c in 0.20 0.31; do
  f=$RUNS/ca/su_${K}_${S}_$it/rule_$c/soak.sdf
  [ -n "$it" ] && [ -f "$f" ] && python3 research/tools/caphold.py "$f" > "$OUT/caphold_$c.txt" 2>&1
done
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
