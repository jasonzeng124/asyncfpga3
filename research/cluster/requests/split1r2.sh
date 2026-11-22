#!/bin/bash
#CLUSTER array=1-24 cores=3 mem=16G time=240
# split1r2: split1's tasks that hit the 240-min limit (BDC_SPLIT_SOURCES=1 through the automatic flow with no kernel
# list), continued from the loop state they sent back (research/data/suite/resume/split1/K_S/; AUTO_RESUME) at this
# commit (CA_FAST: the same proposals, faster; the RAM guard and the seed fallback), draws three at a time.
# PREDICTION (02:10 UTC): collatz64 and ipow finish; ipow's median stays ~6 % under suite6's (split1's first 3 routes:
# 18.98 clean / 20.27 NOT CLEAN vs 21.39 / 21.73), collatz64 within +-5 % of norw1's (pending) -- the split bought
# collatz nothing through the loop (24.24 vs 23.86 on clean routes).
set -uo pipefail
KS=(collatz collatz64 ipow)
K=${KS[$(( (TASK - 1) / 8 ))]}; S=$(( (TASK - 1) % 8 + 1 ))
D=$PWD/research/data/suite/resume/split1/${K}_$S
echo "split1r2 kernel $K seed $S" > "$OUT/task.txt"
[ -f "$D/sizes_1.vh" ] || { echo "nothing to resume ($D)" >> "$OUT/task.txt"; exit 0; }
mkdir -p "$RUNS/state" && cp "$D"/* "$RUNS/state/"
export CA_JOBS=2 DRAW_JOBS=3 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 BDC_SPLIT_SOURCES=1 AUTO_RESUME=$RUNS/state
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 8 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
