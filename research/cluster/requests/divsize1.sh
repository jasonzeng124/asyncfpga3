#!/bin/bash
#CLUSTER array=1-8 cores=2 mem=16G time=180
# divsize1 (subagent divsize, 2026-11-19): test_divui (`var1 / 1083`, Dynamatic's test) through the suite's one command
# on placer seeds 1-8 with rule A's BD_PEERS_CELL (default on since the divsize commit): the request's downstream is what
# it reaches inside its cell, so the divider's datapath behind its own acknowledge (hold = join | z_ack, the bench
# acknowledging out0 combinationally) is measured again.  suite10b tasks 9 / 10 (seeds 1 / 2, before the fix): the loop
# cut the divider's line 159 -> 4-6 links, rule CLEAN, 0 / 4 draws right on both.  Locally after the fix (nextpnr
# 6e5d224472232d5d, the same draw numbers): seeds 1 / 2 / 3 CLEAN at it 2 / 4 / 3 with the line at 332 / 386 / 338 links
# (sdf ecbc22cc / 96c7d776 / 14c880c4), PASS 4 / 4 draws each, 180 / 204 / 186 ns a call (median); seed 4: see the
# subagent's report.  Seeds 1-4 here repeat those (nextpnr reproduces a seed's route); 5-8 are new.
# FILE ONLY AFTER the commit that carries cells/verify/tighten.py's downstream_of() (the tasks check out the branch head).
# PREDICTION: every seed CLEAN with the divider line at 300-400 links and 4 / 4 draws; 180-210 ns a call.
# Locally a task took 45-60 min at 1-2 cores (3-5 routes, their rule steps, the full stack, 4 draws).
set -uo pipefail
K=test_divui; S=$TASK
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0
echo "divsize1 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
for c in 0.20 0.31; do grep -h "udivui0" "$RUNS/ca/su_${K}_${S}_"*/rule_$c/report.txt > "$OUT/divrows_$c.txt" 2>/dev/null; done
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
