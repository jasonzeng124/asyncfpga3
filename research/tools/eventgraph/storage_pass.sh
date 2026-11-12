#!/usr/bin/env bash
# storage_pass.sh KERNEL SIZES_VH SEED VECFILE WORKDIR [ENV...] -- PROGRAM.md FIRST item step 5 (off by default; a
# driver around bdc, no bdc default changes): choose storage from ONE routed pass, the way converge.sh iterates sizes.
#   1. build the bench top with the given sizes (and ENV), from cells/ (hw/build_bench.sh, the board flags)
#   2. the itercost full stack with every net dumped (fullstack_dump.sh), the timed event graph (eventgraph.py)
#   3. search.py: the buildable edits that minimise the graph's period; prints the bdc knobs (ENV line)
#   4. rebuild with those knobs and measure again (same stack): predicted vs measured goes to WORKDIR/result.txt
# The knobs it can emit are bdc's existing ones: BDC_LINK_DEPTHS, BDC_MERGE_OUT_LINK, BDC_LINK_FASTFALL.  Nothing here
# gates a design: the result still needs the full gate (8 routes x 3 corners) before it is a candidate.
set -euo pipefail
K=$1; Z=$2; S=$3; VEC=$(readlink -f "$4"); mkdir -p "$5"; W=$(cd "$5" && pwd); shift 5
R=$(cd "$(dirname "$0")/../../.." && pwd); T=$R/research/tools/eventgraph
cd "$R/cells"; source "${TC:-$HOME/dev2/lib/fpgatoolchain}/openxc7/export.sh" > /dev/null
build() {   # build NAME [ENV...]
    local n=$1; shift
    env "$@" NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES="$Z" ./hw/build_bench.sh "$K" > "$W/build_$n.log" 2>&1
    mkdir -p "$W/hw_$n"; cp build/hw/${K}_bench_gen/${K}_bench_gen{.bit,.sdf,_routed.json} build/gen/${K}_kernel_bench.v "$W/hw_$n/"
    "$T/fullstack_dump.sh" "$W/hw_$n" ${K}_bench_gen "$W/run_$n" "$VEC" > "$W/run_$n.log" 2>&1
    python3 "$T/eventgraph.py" "$W/run_$n" auto --rj "$W/hw_$n/${K}_bench_gen_routed.json" --kv "$W/hw_$n/${K}_kernel_bench.v" | tail -1
}
build base "$@"
python3 "$T/search.py" "$W/run_base/eventgraph" "$Z" | tee "$W/search.txt"
read -r -a KN <<< "$(grep '^ENV ' "$W/search.txt" | cut -c5-)"
pred=$(grep '^chosen' "$W/search.txt" | grep -o '[0-9]* ps' | head -1)
build chosen "$@" "${KN[@]}"
meas=$(grep -o 'period P = [0-9]*' "$W/run_chosen/eventgraph/check.txt")
echo "knobs: ${KN[*]}  predicted: $pred  measured: $meas" | tee "$W/result.txt"
