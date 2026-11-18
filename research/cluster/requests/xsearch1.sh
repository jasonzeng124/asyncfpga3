#!/bin/bash
#CLUSTER array=1-32 cores=3 mem=16G time=240
# xsearch1: flow v6 + AUTO_SEARCH=1 (auto_size.sh's search phase: research/tools/eventgraph/search.py --depth-only on
# the timed event graph of the route the loop ships; if it picks a BDC_LINK_DEPTHS edit, the loop goes on with that
# structure from the shipped sizes, pins empty, at most AUTO_SEARCH_MAXIT routes, and ships the new route only if it is
# clean and its measured P is lower), RESUMED from farm suite6's 32 loop states (research/data/suite/resume/suite6/
# <K>_<S>/, commit f415db410; AUTO_RESUME: the replay stops at once, final() rebuilds the shipped route -- same sdf md5,
# checked in log.txt -- and runs the full stack, then the search phase).  The four original kernels x seeds 1-8, 8 draws
# (K = 10000 + 100 * SEED + j: suite6's draw points), so every task is an A/B against suite6's route of the same seed.
# AUTO_SEARCH_MAXIT=6: suite6's xorshift tasks took 138 min median (99-203) for 8 routes + final + 8 draws on 3 cores,
# i.e. ~11 min per route (collatz64 ~15); this task = rebuild + full stack (~15) + search (1) + at most 6 routes
# (66-120) + full stack (~10) + 8 draws (40-50) = 130-195 min < 220.  Where the search picks nothing the task ends after
# the rebuild and repeats suite6's 8 draws on the same route (~60 min).
# PREDICTION (xorgap, local, nextpnr 6e5d224472232d5d): the search picks BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 on every
# xorshift route (it did on v6 s1, s2, s3, s4, s8 and v3 s8; graph -0.65..-4.55 ns at v6's sizes) and nothing on
# collatz / collatz64 / ipow (best depth edit 0-11 ps on every graph checked: v6 collatz s1, ipow s1, v3 collatz s6,
# ipow s2, collatz64 s5, three older routes), which then ship suite6's routes unchanged.  xorshift P median over the 8
# seeds ~17-18 ns (suite6: 21.07 over 8 routes), every draw passing; collatz64 s1 fails as in suite6 (its loop's it-5
# build missed the bench's 83 MHz; the replay rebuilds it).
set -uo pipefail
KS=(xorshift collatz collatz64 ipow)
K=${KS[$(( (TASK - 1) / 8 ))]}; S=$(( (TASK - 1) % 8 + 1 ))
export CA_JOBS=2 DRAW_JOBS=1 PNR_TIMEOUT=3600 AUTO_SEARCH=1 AUTO_SEARCH_MAXIT=6
mkdir -p "$RUNS/resume_src"; cp -r "research/data/suite/resume/suite6/${K}_$S" "$RUNS/resume_src/su_${K}_$S"
export AUTO_RESUME=$RUNS/resume_src/su_${K}_$S
echo "xsearch1 kernel $K seed $S (resumed from suite6)" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 8 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$RUNS/auto/su_${K}_$S/"*.env "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
