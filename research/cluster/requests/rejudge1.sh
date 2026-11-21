#!/bin/bash
#CLUSTER array=1-12 cores=2 mem=16G time=180
# rejudge1: the routes farm suite1 / suite2 never drew (their fasm_equiv was older: the GND-LUT false alarm, then the
# one-sided fold), rebuilt from the sizes their loops kept (same seed + BDC_AUTO=1 = the same route; checked locally on
# suite1 xorshift s3: sdf ea3c2aad, P 23178, then 4/4) and judged with today's checker: 4 draws each, K = 10000 + 100 S + j.
# Task 12 = suite1 xorshift seed 8 (the route with the first failing draw, K 10804) with 8 draws: how often it fails.
# PREDICTION: the 11 EQUIVALENT, every draw passing except possibly where the route's entry compare is short (formal B7:
# suite1 xorshift s3, UCMPI0 6, fails a slow-carry draw; our 4 default draws may pass it); xorshift s8 fails 1-3 of 8.
set -uo pipefail
read -r K S Z ND <<< "$(sed -n "${TASK}p" research/data/suite/farm/rejudge1.txt)"
export PNR_TIMEOUT=3600
echo "rejudge1 kernel $K seed $S sizes $Z draws $ND" > "$OUT/task.txt"
research/tools/suite/rejudge.sh "$K" "$S" "$Z" "$ND" > "$OUT/summary.txt" 2>&1
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
