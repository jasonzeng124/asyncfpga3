#!/bin/bash
#CLUSTER array=1-32 cores=3 mem=16G time=240
# suite4: the suite's one command on the six original kernels, seeds 1-8, flow v3 (56c8dea81): BDC_AUTO=1; auto_size.sh
# from the estimates x 0.3, the rule (C-element joins) at the draw model's two worst vertices merged per line (chains 0.20,
# rest 0.20 and 0.31, CARRY SLOW_MAX), pinning, MAXIT 4; fasm_equiv with the comparison-only fold; 8 draws per route
# (K = 10000 + 100 S + j), two at a time (gcd / isprime: 4 draws, finish phase 1 route); gcd on gcd8, isprime on isp17.
# Flow as of the commit that picks it up: also the raise-only finish phase (3e93738b1).
# PREDICTION: no draw fails on an EQUIVALENT route (suite1's xorshift s8 failure came from the one-band rule); P medians
# within ~1 ns above suite1's (xorshift ~21.5, collatz ~18.7, collatz64 ~22.5, ipow ~21.5): the second corner added
# ~5 links on xorshift s1.
set -uo pipefail
KS=(xorshift collatz collatz64 ipow)   # gcd / isprime: suite5 (8 cores; their it 0 routes passed 3600 s on 2)
K=${KS[$(( (TASK - 1) / 8 ))]}; S=$(( (TASK - 1) % 8 + 1 ))
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600
echo "suite4 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 600; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
ND=8; export AUTO_FINISH=3
case $K in gcd|isprime) ND=4; AUTO_FINISH=1;; esac   # their simulations are slow: keep the task under its 240 min
research/tools/suite/suite_one.sh "$K" "$S" $ND 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
