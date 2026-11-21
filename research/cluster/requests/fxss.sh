#!/bin/bash
#CLUSTER array=1-32 cores=4 mem=16G time=150
# fxss: the in-cell select race (spec_select.py, abort vs the short line, rule-E form) on fxs's 32 routes (same seeds,
# same build: the route is reproducible). fxs ran before the row existed; everything else about those routes is in fxs.
set -uo pipefail
research/tools/fifteen/spec_select_task.sh fxss_$TASK xorshift research/data/xorshift_sizes_T3s50_fr3_bench.vh $TASK research/data/fifteen/vec_xorshift.hex uaddi0 BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0,n30__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_SPEC_INC=uaddi0:4:6 > "$OUT/log_select.txt" 2>&1
