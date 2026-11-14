#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fxne: xorshift with the != exit test (BDC_FE_EXITCOND's predicate change on the fixture MLIR) + fr2 sizes with
# ucmpi1 8. One route per task, every check (eval_task.sh). Submitted 2026-11-14T05:42Z.
set -uo pipefail
export MLIR_OVERRIDE=research/data/fifteen/xorshift_exitcond_handshake_transformed.mlir
research/tools/fifteen/eval_task.sh fxne_$TASK xorshift research/data/xorshift_sizes_T3s50_fr2ne_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
