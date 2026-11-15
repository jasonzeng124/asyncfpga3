#!/bin/bash
#CLUSTER array=1-8 cores=4 mem=16G time=120
# fneq: rebuild 8 routes whose fasm_equiv said NOT EQUIVALENT (fcol3 s5 s31, fc64h s3 s4 s6, fipowh s2 s7, fxs s6) and
# return fid/equiv.txt, to classify the kinds (the farm's eval.txt kept only the verdict). Same seeds = same routes.
set -uo pipefail
C="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
case $TASK in
 1) A=(collatz research/data/collatz_sizes_T3cdb_nl3_bench.vh 5 $C BDC_NO_LINK=ulink_n28__1) ;;
 2) A=(collatz research/data/collatz_sizes_T3cdb_nl3_bench.vh 31 $C BDC_NO_LINK=ulink_n28__1) ;;
 3) A=(collatz64 research/data/collatz64_sizes_T4cdb_h_bench.vh 3 $C BDC_NO_LINK=ulink_n30__1) ;;
 4) A=(collatz64 research/data/collatz64_sizes_T4cdb_h_bench.vh 4 $C BDC_NO_LINK=ulink_n30__1) ;;
 5) A=(collatz64 research/data/collatz64_sizes_T4cdb_h_bench.vh 6 $C BDC_NO_LINK=ulink_n30__1) ;;
 6) A=(ipow research/data/ipow_dsp1_sizes_T9s75_h_bench.vh 2 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0) ;;
 7) A=(ipow research/data/ipow_dsp1_sizes_T9s75_h_bench.vh 7 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0) ;;
 8) A=(xorshift research/data/xorshift_sizes_T3s50_fr3_bench.vh 6 BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0,n30__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_SPEC_INC=uaddi0:4:6) ;;
esac
K=${A[0]}; N=fneq_$TASK
V=research/data/fifteen/vec_${K}.hex; [ -f $V ] || V=research/data/fifteen/vec_collatz.hex
research/tools/fifteen/lane2.sh "q$TASK" "$N" "$K" "${A[1]}" "${A[2]}" "$V" "${A[@]:3}" > "$OUT/summary.txt" 2>&1
cp "$RUNS/r/$N/fid/equiv.txt" "$OUT/" 2>/dev/null
md5sum "$RUNS/hw/$N/${K}_bench_gen.sdf" >> "$OUT/summary.txt" 2>/dev/null
