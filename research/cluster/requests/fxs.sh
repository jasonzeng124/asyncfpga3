#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fxs: item 23 (xf4) + the speculative-completion incrementer BDC_SPEC_INC=uaddi0:4:6. Every check, the static check
# per case (SPEC_CASES: LONG / SHORT at nominal and worst), the hold check. Period: the latency line (the event graph
# has no single period with data-dependent iterations). Compare with fxf4 seed by seed.
set -uo pipefail
export HOLD_VEC=research/data/fifteen/vec_xorshift_hold.hex SPEC_CASES=uaddi0:4
research/tools/fifteen/eval_task.sh fxs_$TASK xorshift research/data/xorshift_sizes_T3s50_fr3_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0,n30__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_SPEC_INC=uaddi0:4:6 > "$OUT/log_eval.txt" 2>&1
