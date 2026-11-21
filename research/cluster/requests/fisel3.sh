#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fisel3: as fisel0 but the select links sized by rule E (h4s3 sizes file: see its first line). Every check incl. hold_bits and TSE; compare latency with the h4 base (fipowh4 / fc64eq3) seed by seed. Submitted 2026-11-16.
set -uo pipefail
export HOLD_VEC=research/data/fifteen/vec_ipow_hold.hex TSE_VEC=research/data/fifteen/vec_ipow.hex
research/tools/fifteen/eval_task.sh fisel3_$TASK ipow research/data/ipow_dsp1_sizes_T9s75_h4s3_bench.vh $TASK research/data/fifteen/vec_ipow.hex research/data/eventgraph/gate/ipow17.hex research/data/eventgraph/gate/ipow17.exp BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
