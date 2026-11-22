#!/bin/bash
#CLUSTER array=1-48 cores=2 mem=16G time=240
# suite2: the suite's one command (research/tools/suite/suite_one.sh) on the six original kernels, seeds 1-8, with the
# flow as of this commit: BDC_AUTO=1; auto_size.sh starting at emit.py's estimates x 0.3 (AUTO_START_SCALE), the rule
# with C-element joins, pinning only lines ever lengthened, on while a clean route still shortens, MAXIT 4; the bits
# judged by the fixed fasm_equiv (745cb181a: suite1 ran before it and called the GND-LUT kind NOT EQUIVALENT); 4 draws
# per route (K = 10000 + 100 S + j); gcd on gcd8, isprime on isp17, one-vector period runs for both.
# PREDICTION (written before any scaled-start route): every EQUIVALENT ffmux-clean route passes 4 / 4 draws; P median
# within 1 ns of the seed-1 routes of the estimates start (xorshift 21.1, collatz 18.1, collatz64 30.0), fewer
# PNR timeouts (none expected), and most loops clean by it 4.
set -uo pipefail
KS=(xorshift collatz collatz64 ipow gcd isprime)
K=${KS[$(( (TASK - 1) / 8 ))]}; S=$(( (TASK - 1) % 8 + 1 ))
export CA_JOBS=2 DRAW_JOBS=1 PNR_TIMEOUT=3600
echo "suite2 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 600; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
