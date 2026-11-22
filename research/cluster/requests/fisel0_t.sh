#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fisel0_t: TSE_ONLY rerun of fisel0 (same seeds = same routes): the first run's step 5 was void (stride-2 graphs, JOURNAL 18:03).
# fisel0: ipow h4 (fipowh4's knobs) with the select links' DELAY at 0 (ipow_dsp1_sizes_T9s75_h4s0_bench.vh; the select rule is withdrawn, PROGRAM 2026-11-15). Every check incl.
# hold_bits and TSE (step 5). The owner's bar: the select checks must FAIL on a raced select in each kernel family --
# this is that family's attempt; if no route races, it is the gain. Submitted 2026-11-15T17:24Z.
set -uo pipefail
export TSE_ONLY=1 HOLD_VEC=research/data/fifteen/vec_ipow_hold.hex TSE_VEC=research/data/fifteen/vec_ipow.hex
research/tools/fifteen/eval_task.sh fisel0_t_$TASK ipow research/data/ipow_dsp1_sizes_T9s75_h4s0_bench.vh $TASK research/data/fifteen/vec_ipow.hex research/data/eventgraph/gate/ipow17.hex research/data/eventgraph/gate/ipow17.exp BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
