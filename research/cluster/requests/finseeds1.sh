#!/bin/bash
#CLUSTER array=1-40 cores=3 mem=16G time=240
# finseeds1: does the sizing loop's finish phase converge with more draws per step and more steps (arm DA), or with
# more steps alone (arm A)? Twenty loops that ended NOT CLEAN after the three raise-only routes (norw1, split1 with
# BDC_SPLIT_SOURCES=1, suite9r3; none tested locally by subagent converge; research/data/suite/resume/finseeds1/R_K_S:
# the farm's own files, minus lines_* / ca_*).
#   tasks 1-20, arm DA: resumed at the START of the finish phase (research/tools/suite/finish_state.sh: files up to
#     it 4, sizes_5), AUTO_FINISH=6 AUTO_FINISH_SEEDS=3 AUTO_FINISH_JOBS=2: each finish route the rule finds not clean is
#     drawn again on seeds S+1000 and S+2000 (built at once), the first clean one is adopted; up to six raise-only
#     steps (it 5-10). Its it 5 on seed S is the farm's own route 5 (md5 checked below, as it5_check), and so is every
#     later seed-S route until an adoption: the farm run is the control for the steps it built.
#   tasks 21-40, arm A: the same loops resumed from the farm's state after it 7 (sizes_8) with AUTO_FINISH=6 and no
#     extra seeds: three more raise-only routes (it 8-10), the plain loop given more steps.
# Both arms ship the LEAST SHORT route when none is clean (AUTO_SHIP_LEAST=1: the smallest total miss over the routes
# the loop built), which suite_one.sh then judges with its 8 draws; the farm's own run judged the last route.
# Why (research/data/converge/notes.txt): 95 % of the rows short on a finish route are on constraints no earlier finish
# route had short, and a re-route moves a margin by sd ~0.5 ns with none of its lines changed, so headroom on the raised
# lines cannot converge it; each finish route is a fresh draw. Local pilot (nextpnr 6e5d224472232d5d; 5 loops, 5
# kernels, each replaying its farm run exactly: md5 and rule rows of every resumed it 5 identical): draws at it 5-7
# made 2 of 5 CLEAN (after 6 and 3 extra routes), one more raise-only step (it 8, seed S) made 4 of 5 CLEAN, both
# together 5 of 5; P of the clean routes against the farm's NOT CLEAN ones median +0.07 ns (-0.36 .. +1.20, route
# scatter); +2..+3 delay elements per extra raise step, none per adopted draw. On the farm's NOT CLEAN loops an earlier
# route was less short than the shipped last one on 64 of 135; ringfuse1/31's it 6 (2 rows) passes draw 10707, which
# its shipped it 7 (9 rows to -1019 ps) fails.
# Seed-S routes carry fewer short rows than other seeds at the same sizes (3.9 vs 8.7 per route over 19 / 34 routes:
# the raise-only steps pad what that seed's routes had short), so new seeds are clean rarely (2 of 40 draws locally).
# PREDICTION (subagent converge, 2026-11-19 ~15:50 UTC, from the local pilot): arm A >= 11 of 20 CLEAN by it 10 (the
# 12 norw1 / split1 loops mostly at it 8, the suite9r3 loops with 4-14 rows per route seldom); arm DA CLEAN on every
# loop arm A is (same seed-S routes until an adoption) plus 1-3 more, at ~20 extra routes per adopted draw; median P of
# the clean routes within 0.5 ns of the same loops' NOT CLEAN farm routes, each within +-1.5 ns; delay elements +2..+3
# per extra step; every judged route (clean, or the least short) passes its 8 draws.
set -uo pipefail
SPEC=("norw1_xorshift_8 -" "norw1_collatz_2 -" "norw1_collatz_3 -" "norw1_collatz64_4 -" "norw1_collatz64_5 -"
      "norw1_collatz64_8 -" "split1_collatz_4 BDC_SPLIT_SOURCES=1" "split1_collatz_6 BDC_SPLIT_SOURCES=1"
      "split1_collatz64_2 BDC_SPLIT_SOURCES=1" "split1_collatz64_5 BDC_SPLIT_SOURCES=1" "split1_ipow_2 BDC_SPLIT_SOURCES=1"
      "split1_ipow_5 BDC_SPLIT_SOURCES=1" "suite9r3_sqrtsub_1 -" "suite9r3_quadrec_1 -" "suite9r3_quadrec_4 -"
      "suite9r3_branchloop_2 -" "suite9r3_dot2_3 -" "suite9r3_iterative_division_3 -" "suite9r3_if_loop_2_4 -"
      "suite9r3_twoloops_1 -")
NL=${#SPEC[@]}; J=$(( (TASK - 1) % NL )); ARM=DA; [ "$TASK" -gt "$NL" ] && ARM=A
read -r DIR XE <<< "${SPEC[$J]}"; [ "$XE" = - ] && XE=""
K=${DIR#*_}; S=${K##*_}; K=${K%_*}                     # R_K_S, K may hold underscores
D=$PWD/research/data/suite/resume/finseeds1/$DIR
echo "finseeds1 arm $ARM kernel $K seed $S ($DIR) $XE" > "$OUT/task.txt"
[ -f "$D/sizes_5.vh" ] || { echo "no state ($D)" >> "$OUT/task.txt"; exit 0; }
mkdir -p "$RUNS/state"
if [ "$ARM" = DA ]; then
  research/tools/suite/finish_state.sh "$D" "$RUNS/state" >> "$OUT/task.txt"
  export AUTO_FINISH_SEEDS=3 AUTO_FINISH_JOBS=2
else
  cp "$D"/* "$RUNS/state/"
fi
export CA_JOBS=1 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 AUTO_RESUME=$RUNS/state AUTO_FINISH=6 AUTO_SEARCH=0 \
  AUTO_SHIP_LEAST=1
[ -n "$XE" ] && export "$XE"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 8 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
if [ "$ARM" = DA ]; then   # the control: the resumed seed-S route 5 is the farm's own (it_5s0.txt if an alternate took it 5)
  A5=$RUNS/auto/su_${K}_$S/it_5s0.txt; [ -f "$A5" ] || A5=$RUNS/auto/su_${K}_$S/it_5.txt
  G5=$(awk '{print $2}' "$A5" 2>/dev/null); W5=$(awk '{print $2}' "$D/it_5.txt")
  echo "it5_check: rebuilt $G5, farm $W5 -> $([ "$G5" = "$W5" ] && echo SAME || echo DIFFERENT)" >> "$OUT/task.txt"
fi
grep -E '^(alt|adopt|it [5-9] |it 10 |final)' "$RUNS/auto/su_${K}_$S/log.txt" 2>/dev/null | cut -c1-160 >> "$OUT/task.txt"
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
