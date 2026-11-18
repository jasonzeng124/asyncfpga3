#!/bin/bash
#CLUSTER array=1-64 cores=2 mem=16G time=240
# suite3: the suite's one command on the 16 suite kernels (kernels/SUITE.md: 14 new shapes + nested + branchloop),
# seeds 1-4, with the flow as of this commit (BDC_AUTO=1, auto_size.sh started at the estimates x 0.3, C-element joins,
# pinning, MAXIT 4; fasm_equiv with the comparison-only fold, 601010f1b), 4 draws per route on kernels/K/vec.hex,
# expected values compiled from the C (research/tools/suite/oracle.sh). digitsum / digitdiv do not compile (expected:
# status DOES-NOT-COMPILE, fast).
# PREDICTION (from suitek's seed-1 smoke routes, default sizes): straight, countloop, sqrtsub, twoloops, brhash, horner,
# fold64, varshift, cmpchain, nested, branchloop pass 4 / 4 on every EQUIVALENT route; quadrec HANGS on every route (a
# bdc ring-floor bug: 4 tokens on 4 stages); lfsrfind and nest3 unknown (their AUTO smoke routes were FFMUX-flagged).
set -uo pipefail
KS=(straight countloop sqrtsub nest3 twoloops brhash lfsrfind quadrec horner fold64 varshift cmpchain nested branchloop digitsum digitdiv)
K=${KS[$(( (TASK - 1) / 4 ))]}; S=$(( (TASK - 1) % 4 + 1 ))
export CA_JOBS=2 DRAW_JOBS=1 PNR_TIMEOUT=3600
echo "suite3 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 600; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
