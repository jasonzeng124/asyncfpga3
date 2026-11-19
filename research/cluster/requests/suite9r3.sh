#!/bin/bash
#CLUSTER array=1,2,9,10,11,12,13,14,16,22,23,26,28,30,31,34,35,36,37,38,39,40,41,43,47,54,55,56,57,58,59,60,62,63,64,65,67,68,78,79,80,82,83,84,85,86,87,88,89,90,91,92 cores=2 mem=16G time=240
# suite9r3 (suite9r2 re-filed with only the tasks that have a state: as array=1-92 it waited 4.5 h for 184 free cores while smaller requests went ahead): suite9's tasks that hit the 240-minute limit, continued from the loop state they sent back
# (research/data/suite/resume/suite9/K_S/, copied from claude/cluster results/suite9/TASK/auto/), with auto_size.sh's
# AUTO_RESUME, at this commit: the rule and the loop are suite9's (eaef0dec7) plus the bench-clock seed fallback (an
# iteration whose bench side misses 83 MHz is rebuilt on seed S+100, S+200 instead of ending the loop -- suite9's
# varshift s4 died that way at it 3), and opt-in phases left off. Tasks whose loop died on a missed bench clock are
# resumed too. A task with no state in the repo (its loop finished in suite9, or nothing came back) exits at once.
# Checked before filing: suite3a's straight seed 3 cut after it 2 and resumed on the cluster rebuilt it 3 / it 4 with the
# farm's sdf md5s (b185f449 / 4896c89d), the same ratchet lines, and ended CLEAN it=4 as the farm run did.
# PREDICTION (21:39 UTC): every resumed loop rebuilds its last route with the same sdf md5 as suite9 returned (log.txt says
# "rebuilt" only for the shipped route); most of the loops finish (CLEAN or NOT CLEAN after the finish phase) within
# 240 min; every judged route passes its 4 draws.
set -uo pipefail
KS=(sqrtsub nest3 twoloops quadrec horner fold64 varshift cmpchain nested branchloop memsum dot2 gather fill factorial
    iterative_division iterative_sqrt test_loop_free test_bitint if_loop_1 if_loop_2 sumi3_mem fir)
K=${KS[$(( (TASK - 1) / 4 ))]}; S=$(( (TASK - 1) % 4 + 1 ))
D=$PWD/research/data/suite/resume/suite9/${K}_$S
echo "suite9r3 kernel $K seed $S" > "$OUT/task.txt"
[ -f "$D/sizes_1.vh" ] || { echo "nothing to resume ($D)" >> "$OUT/task.txt"; exit 0; }
mkdir -p "$RUNS/state" && cp "$D"/* "$RUNS/state/"
export CA_JOBS=2 DRAW_JOBS=1 PNR_TIMEOUT=3600 AUTO_RESUME=$RUNS/state
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
