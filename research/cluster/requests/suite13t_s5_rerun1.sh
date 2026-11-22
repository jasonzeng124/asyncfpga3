#!/bin/bash
#CLUSTER array=1-8 cores=2 mem=16G time=240
# suite13t_s5_rerun1: the tasks the farm lost to node node-c1, which failed every task it got at container creation
# ("mount proc->/proc error ... operation not permitted", exit 255 in 4-11 s): the same kernel, seed and flow as the task
# lost. exit1 (the != loop-test fixtures, flow v9, no trim): sumi3_mem s3 (task 91), nested_loop s3 (105). suite13t
# (flow v9 + the trim step): fold64 s1 (s1a 16), nested s1 (s1a 19), sqrtsub s2 (s2a 9), nest3 s2 (s2a 10), test_divui s2
# (s2a 25), memsum s2 (s2a 26). Result lines are read with their request's own (suite_table.py / pair_cmp.py).
set -uo pipefail
ROWS=("exit1 sumi3_mem 3" "exit1 nested_loop 3" "suite13t fold64 1" "suite13t nested 1" "suite13t sqrtsub 2" "suite13t nest3 2" "suite13t test_divui 2" "suite13t memsum 2")
read -r Q K S <<< "${ROWS[$((TASK - 1))]}"
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1
if [ "$Q" = exit1 ]; then cp cloud/fixtures/frontend_exitcond/$K/comp/*.mlir build/frontend/$K/comp/; else export AUTO_TRIM=1; fi
echo "suite13t_s5_rerun1 ($Q) kernel $K seed $S" > "$OUT/task.txt"
md5sum build/frontend/$K/comp/handshake_transformed.mlir >> "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
rm -f "$OUT/auto/"place_*.txt
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
