#!/bin/bash
#CLUSTER array=1,3 cores=4 mem=16G time=90
# First request, filed with the farm itself (2026-11-14): the xfr candidate, seeds 1 and 3.
# It must come back as graphs/xfr_1 and graphs/xfr_3: SDF 90890b3b, P=22523 and SDF f5e13316, P=23581.
set -uo pipefail
N=farm_check_$TASK
research/tools/fifteen/lane.sh "fcL$TASK" "$N" xorshift research/data/xorshift_sizes_T3s50_fr_bench.vh "$TASK" \
    research/data/fifteen/vec_xorshift.hex BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 \
    BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 \
    BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/summary.txt" 2>&1
rc=$?
G=research/data/eventgraph/graphs/$N
cp "$G"/check.txt "$G"/benchres.txt "$G"/build.txt "$G"/provenance.txt "$OUT/" 2>/dev/null
exit $rc
