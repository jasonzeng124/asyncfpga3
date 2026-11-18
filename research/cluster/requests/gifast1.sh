#!/bin/bash
#CLUSTER array=1-8 cores=8 mem=32G time=240
# gifast1: suite7 again (gcd and isprime x seeds 1-4, 8 cores, CA_JOBS=4, 4 draws) with CA_FAST=1 and the default finish phase:
# the same sizing rule, its audits memoized exactly and forked from the base run (research/tools/ca_fast.py; the
# rule's outputs byte-identical to the old path's on the routes in research/data/loopfast/).  The ONLY change against
# suite7 is CA_FAST=1 (and the head).  Measured locally (loopfast, 16-core node at load ~20): gcd seed 1 it 0
# (route f72c44e4, = suite7 task 1's) the rule step 1268 / 1330 s CPU per corner with one fork per corner (26 / 25 min
# wall), its sizes_1.vh identical to suite7's; isprime seed 1 it 0-2 routes = suite7 task 5's, the step 13.9 min wall
# (both corners side by side, one fork each).  PREDICTION: every task's loop ends inside 240 min (suite7: 6 of 8 hit the
# limit; gcd finished one rule step in 4 h); a gcd rule step ~6-10 min on 8 cores (CA_JOBS=4), isprime ~4-6.
# mem 32G: CA_FAST keeps the base run in memory and forks it (gcd: main ~2.3 GB, each fork up to ~1.8 GB private;
# 2 corners x (2.3 + 4 x 1.8) ~ 19 GB at CA_JOBS=4, research/data/loopfast/mem.txt).
# auto/mtimes.txt: the auto directory's file times (epoch s), for the time of each build and each rule step.
set -uo pipefail
KS=(gcd isprime)
K=${KS[$(( (TASK - 1) / 4 ))]}; S=$(( (TASK - 1) % 4 + 1 ))
export CA_FAST=1 CA_JOBS=4 DRAW_JOBS=2 PNR_TIMEOUT=7200
echo "gifast1 kernel $K seed $S start $(date +%s)" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
snap() { cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
         ls -l --time-style=+%s "$RUNS/auto/su_${K}_$S/" > "$OUT/auto/mtimes.txt" 2>/dev/null; }
( while sleep 600; do snap; done ) & BG=$!
ND=4   # the flow's own finish phase (AUTO_FINISH default 3, as for every kernel: suite7's AUTO_FINISH=1 for gcd / isprime was a per-kernel setting, auditor T161)
research/tools/suite/suite_one.sh "$K" "$S" $ND 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
snap
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
echo "end $(date +%s)" >> "$OUT/task.txt"
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
