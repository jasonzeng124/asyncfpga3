#!/bin/bash
#CLUSTER array=1-8 cores=2 mem=16G time=240
# conv1: does the sizing loop's finish phase converge when it also pads the lines that are NEAR their limit?
# Eight of suite6's 16 loops that ended NOT CLEAN after the three raise-only routes (flow v6, the same code for these
# kernels: bdc emits them byte-identically since, corner_audit's only change is for memory lines), resumed from their
# state after it 3 (research/data/suite/resume/conv1/K_S: suite6's files, pins rebuilt from ratchet_2 / ratchet_3) with
# AUTO_NEAR_PS=300: in the finish phase every line the rule keeps at its size with < 300 ps left at a corner gets the
# headroom element too (ratchet.py --near). The control is suite6's own run of the same seed (no near padding): it 4
# is rebuilt here first and must have suite6's sdf md5 (written below as it4_check).
# PREDICTION (2026-11-18 17:54 UTC, before any result): at least 5 of 8 end CLEAN within the three finish routes (suite6:
# 0 of these 8); the P of the shipped route within ~0.5 ns of suite6's last route for the same seed (median over the 8);
# every route judged passes its 8 draws.
set -uo pipefail
SPEC=("collatz 1 105a67bd" "collatz 2 e4d72cde" "collatz64 5 983940f4" "collatz64 7 8773820c" "ipow 1 45f57639"
      "ipow 4 db73c076" "xorshift 2 b27b9c8a" "xorshift 7 65ac4510")
read -r K S W4 <<< "${SPEC[$((TASK - 1))]}"
echo "conv1 kernel $K seed $S (suite6 it 4 sdf $W4)" > "$OUT/task.txt"
mkdir -p "$RUNS/state" && cp research/data/suite/resume/conv1/${K}_$S/* "$RUNS/state/"
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 AUTO_RESUME=$RUNS/state AUTO_NEAR_PS=300
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 8 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
G4=$(awk '{print $2}' "$RUNS/auto/su_${K}_$S/it_4.txt" 2>/dev/null)
echo "it4_check: rebuilt $G4, suite6 $W4 -> $([ "$G4" = "$W4" ] && echo SAME || echo DIFFERENT)" >> "$OUT/task.txt"
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
