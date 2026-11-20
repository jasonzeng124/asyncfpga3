#!/bin/bash
#CLUSTER array=1-32 cores=2 mem=16G time=240
# suite13t_s1c_arw: formal's PROVED loop-test passes through flow v9 + the trim step (suite13t's exact environment),
# on the 8 suite kernels where a pass is proved, seeds 1-4: suite13t's same (kernel, seed) is the control.
# The MLIR each task builds is research/data/autorw/K.mlir: the output of formal's formal/tools-A/rewrite/plain_pass.py
# (the plain loop-test move, i + 1 < n -> i < n - 1: xorshift, countloop, twoloops, quadrec, horner, varshift) or
# eq2_pass.py (the test on the update -> the test on the value: collatz, collatz64), run on this branch's default
# fixtures at origin/claude/formal 2a34c3dfb, matched by structure (no names, no hashes), each kept only because Lean
# proved it equal to the input graph (token level; import with BDC_RING_FUSE=0, research/data/autorw/census.txt).
# RTL bench against the C, all 8: PASS (xorshift 19/19, collatz 17/17, collatz64 18/18, countloop 10/10, twoloops 11/11,
# quadrec 10/10, horner 11/11, varshift 10/10). Named so it sorts after suite13t's seed 1 and before its seeds 2-4.
# PREDICTION (2026-11-20 11:05 UTC, before any result of this request or of the local loops): xorshift: the fused
# update + test line (18 elements on suite13t s1) shorter by 4-8 and P 1.5-3 ns below suite13t's same seed; collatz /
# collatz64: P 15-25 % below suite13t's (the md5-keyed versions gave -24 / -26 % before ring fusion); countloop 5-10 %
# below; twoloops / quadrec / horner / varshift within route scatter (+-5 %); every draw passes; rule-clean share as
# suite13t's.
set -uo pipefail
KS=(xorshift collatz collatz64 countloop twoloops quadrec horner varshift)
NK=${#KS[@]}
K=${KS[$(( (TASK - 1) % NK ))]}; S=$(( (TASK - 1) / NK + 1 ))
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1
export MLIR_OVERRIDE=research/data/autorw/$K.mlir
echo "suite13t_s1c_arw kernel $K seed $S (MLIR_OVERRIDE=$MLIR_OVERRIDE)" > "$OUT/task.txt"
md5sum "$MLIR_OVERRIDE" >> "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
rm -f "$OUT/auto/"place_*.txt
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
