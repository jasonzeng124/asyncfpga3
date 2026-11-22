#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fc64sel3: as fc64sel0 but the select links sized by rule E (h4s3 sizes file: see its first line). Every check incl. hold_bits and TSE; compare latency with the h4 base (fipowh4 / fc64eq3) seed by seed. Submitted 2026-11-16.
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex TSE_VEC=research/data/fifteen/vec_collatz.hex
research/tools/fifteen/eval_task.sh fc64sel3_$TASK collatz64 research/data/collatz64_sizes_T4cdb_h4s3_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
