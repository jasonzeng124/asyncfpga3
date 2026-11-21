#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fxf2: one route per task, every check (research/tools/fifteen/eval_task.sh): build + itercost period, the static
# check at nominal and worst (owner's full-range rule), the 3-corner gate. Submitted 2026-11-14T05:35Z.
set -uo pipefail
research/tools/fifteen/eval_task.sh fxf2_$TASK xorshift research/data/xorshift_sizes_T3s50_fr2_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
