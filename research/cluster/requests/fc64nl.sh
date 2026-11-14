#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fc64nl: one route per task, every check (research/tools/fifteen/eval_task.sh): build + itercost period, the static
# check at nominal and worst (owner's full-range rule), the 3-corner gate. Submitted 2026-11-14T05:35Z.
set -uo pipefail
research/tools/fifteen/eval_task.sh fc64nl_$TASK collatz64 research/data/collatz64_sizes_T4cdb_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_NO_LINK=ulink_n30__1 > "$OUT/log_eval.txt" 2>&1
