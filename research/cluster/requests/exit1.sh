#!/bin/bash
#CLUSTER array=1-140 cores=2 mem=16G time=240
# exit1: the != loop test (LLVM indvars' own exit-test rewrite, bdc/frontend.sh BDC_FE_EXITCOND=1: the fixtures in
# cloud/fixtures/frontend_exitcond/, made with the owner's Dynamatic on the cluster) on the 35 suite kernels whose
# frontend output it changes (sobel / video_filter left out: their loops do not fit 240 min), seeds 1-4, through the
# same flow as suite13 (v8 + the ucap rule fix + CA_BENCHCAP=1): suite13's same kernels and seeds are the control.
# PREDICTION (2026-11-20 02:03 UTC; first local route: xorshift s1 it 5, fused update + test 11 elements / 4.1 ns against 15 /
# 5.8 on the default fixture's route, P 17.22 vs 18.11 ns, EQUIVALENT): on the 11 kernels where only the loop test's
# predicate changes (slt -> ne), the fused cell's line is 2-5 elements shorter and the median P over 4 seeds 0.5-2 ns
# below suite13's; on the kernels indvars restructures, no prediction of speed; every draw passes on every kernel
# (LLVM's proof; the draws check it against the C).
set -uo pipefail
KS=(xorshift gcd isprime countloop nest3 twoloops brhash lfsrfind quadrec horner fold64 varshift nested memsum dot2 gather fill test_bitint if_loop_1 if_loop_2 sumi3_mem fir test_memory_1 test_memory_2 mul_example share_test_2 test_stdint spmv test_flatten_array image_resize vector_rescale stencil_2d iir share_test_1 nested_loop)
NK=${#KS[@]}
K=${KS[$(( (TASK - 1) % NK ))]}; S=$(( (TASK - 1) / NK + 1 ))
cp cloud/fixtures/frontend_exitcond/$K/comp/*.mlir build/frontend/$K/comp/
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1
echo "exit1 kernel $K seed $S (frontend: BDC_FE_EXITCOND=1)" > "$OUT/task.txt"
md5sum build/frontend/$K/comp/handshake_transformed.mlir >> "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
