#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fceq_la: item 25 (fceq's sizes and seeds): every delay line on the loop, line_account.py at worst and nominal, 32 routes (PROGRAM second lead; >= 8 routes asked). Static + TSE as well.
# fceq: collatz, the loop test reads n == 2 instead of n' == 1 (research/tools/fifteen/pre_eq2.py; exact on every input), nl4 sizes, item 22 knobs less the dropped link (n28 is gone). Static check with C-element joins. Compare with fcol4 seed by seed.
set -uo pipefail
export STATIC_ONLY=1 LINE_ACCT=1 TSE_VEC=research/data/fifteen/vec_collatz.hex BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz_preeq2.mlir
export STATIC_ONLY=1 LINE_ACCT=1 TSE_VEC=research/data/fifteen/vec_collatz.hex HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex
research/tools/fifteen/eval_task.sh fceq_la_$TASK collatz research/data/collatz_sizes_T3cdb_nl4_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/col13.hex research/data/eventgraph/gate/col13.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
