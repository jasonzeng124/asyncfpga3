#!/bin/bash
#CLUSTER array=1-32 cores=4 mem=16G time=90
# fxf4l: the latency line for item 23 (xf4) on seeds 1-32 -- the baseline fxs is compared with (build + itercost run only).
set -uo pipefail
research/tools/fifteen/lane2.sh "lL$TASK" fxf4l_$TASK xorshift research/data/xorshift_sizes_T3s50_fr3_bench.vh $TASK research/data/fifteen/vec_xorshift.hex BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0,n30__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/summary.txt" 2>&1
grep -o 'latmin=[0-9]*' "$RUNS/r/fxf4l_$TASK/run.log" | head -1 >> "$OUT/summary.txt"
