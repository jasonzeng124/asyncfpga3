#!/bin/bash
#CLUSTER array=1-92 cores=2 mem=16G time=240
# suite9: the suite's one command on every compiling kernel that has fewer than 4 judged routes (23 kernels x seeds 1-4),
# flow v6 as of this commit (BDC_AUTO=1, auto_size.sh: start x 0.3, the two-corner rule with C-element joins, join
# credit, steer self-bound, token floor, finish phase; nextpnr 6e5d224472232d5d), 4 draws per route, expected values
# from the C; memory kernels judged with every array read back (GATE_MEMEXP). Not here: the four original fast kernels
# (suite6: 8 seeds each), straight / countloop / lfsrfind / brhash / test_int16 / unused_arg (suite3a / 3b: 4 / 4 each),
# gcd / isprime (the loop is too slow for them; subagent loopfast), digitsum / digitdiv (do not compile; subagent divmod).
# NEW: the loop can continue in a later request (auto_size.sh AUTO_RESUME): the copier below sends back the loop's state
# every 5 minutes (sizes_I.vh, pinned_I.txt, ratchet_I.txt, rule_I.vh, neg_I.txt, log.txt); a follow-up request
# (suite9r2) resumes every task that hit the time limit from what came back, at this commit's flow.
# PREDICTION (from suite3a / 3b / 8, 2 cores, same flow): sqrtsub, horner, test_loop_free, test_bitint, dot2, gather and
# fill finish within 240 min on most seeds; nest3, twoloops, nested, cmpchain, branchloop, fold64, varshift, factorial,
# iterative_division, iterative_sqrt, memsum, if_loop_1 / 2, sumi3_mem, fir time out in the loop on most seeds (60-80
# min per iteration); quadrec may fail the bench's 83 MHz on some routes (BUILD-FAILED, as suite3a seed 2); every route
# that is judged passes its draws.
set -uo pipefail
KS=(sqrtsub nest3 twoloops quadrec horner fold64 varshift cmpchain nested branchloop memsum dot2 gather fill factorial
    iterative_division iterative_sqrt test_loop_free test_bitint if_loop_1 if_loop_2 sumi3_mem fir)
K=${KS[$(( (TASK - 1) / 4 ))]}; S=$(( (TASK - 1) % 4 + 1 ))
export CA_JOBS=2 DRAW_JOBS=1 PNR_TIMEOUT=3600
echo "suite9 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
