#!/usr/bin/env bash
# run_default.sh KERNEL SEED VEC [GATEVEC GATEEXP] -- one DEFAULT-flow bench route of KERNEL (research/data/alltable/README.md):
#   cells/hw/build_bench.sh KERNEL with BD_NO_TIGHTEN=1 BD_SIZES=none (no BDC_* knob, no sizes file: every matched delay
#   at bdc/emit.py's own estimate), BD_DSP=1, NEXTPNR_SEED=SEED, --freq 83 (build_bench's TARGET_MHZ default);
#   then the itercost full stack (fullstack_dump.sh) on VEC and the timed event graph (eventgraph.py) -> period P;
#   with GATEVEC / GATEEXP also bench_gate.sh at the worst corner (chains 0.21, CARRY4/F7F8/FF 1, rest 0.288, + M).
# Same steps as research/tools/fifteen/lane2.sh, but builds in a plain copy of cells/ bdc/ build/frontend (no git
# worktree: this agent runs no state-changing git command). Output under $RUNS (default: scratch).
# Prints: KERNEL SEED sdf-md5 P=<ps> odata verdict [gate ...]
set -euo pipefail
K=$1; S=$2; VEC=$(readlink -f "$3"); GV=${4:-}; GE=${5:-}
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:?set RUNS}
T=$RUNS/tree; N=${K}_s$S; HW=$RUNS/hw/$N; RD=$RUNS/r/$N
if [ ! -d "$T/cells" ]; then mkdir -p "$T/build"; cp -r "$R/cells" "$R/bdc" "$T/"; cp -r "$R/build/frontend" "$T/build/"; fi
source "${TC:-$HOME/dev2/lib/fpgatoolchain}/openxc7/export.sh" > /dev/null
mkdir -p "$HW" "$RD"
( cd "$T/cells" && rm -rf build/hw/${K}_bench_gen && env NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES=none \
    ./hw/build_bench.sh "$K" ) > "$HW/build.log" 2>&1 || { echo "$K $S BUILD FAILED ($HW/build.log)"; exit 1; }
B=$T/cells/build/hw/${K}_bench_gen
cp "$B/${K}_bench_gen".{bit,sdf,fasm} "$B/${K}_bench_gen_routed.json" "$B/toolchain.txt" "$T/cells/build/gen/${K}_kernel_bench.v" "$HW/"
grep -h "Max frequency for clock" "$B/pnr.log" 2>/dev/null | tail -2 > "$HW/fmax.txt" || true
md5=$(md5sum "$HW/${K}_bench_gen.sdf" | cut -c1-8)
ff=$(python3 "$R/research/tools/ffmux_scan.py" "$HW/${K}_bench_gen.fasm" > "$HW/ffmux.txt" 2>&1 && echo ffmux-clean || echo FFMUX-FLAG)
"$R/research/tools/eventgraph/fullstack_dump.sh" "$HW" ${K}_bench_gen "$RD" "$VEC" > "$RD/dump.log" 2>&1 || true
python3 "$R/research/tools/eventgraph/eventgraph.py" "$RD" auto --rj "$HW/${K}_bench_gen_routed.json" \
    --kv "$HW/${K}_kernel_bench.v" > "$RD/eventgraph.log" 2>&1 || true
rm -f "$RD/dump.vcd" "$RD/netlist_baked.v"
P=$(grep -o 'period P = [0-9]*' "$RD/eventgraph/check.txt" 2>/dev/null | grep -o '[0-9]*$' || echo NA)
od=$(grep BENCHRES "$RD/run.log" | grep -o 'odata=[0-9a-f]*\|cycles=[0-9]*' | tr '\n' ' ')
v=$(grep -o 'VERDICT: [A-Z ]*' "$RD/fid/equiv.txt" 2>/dev/null | head -1 || echo "VERDICT ?")
g=""
if [ -n "$GV" ]; then
  g=$("$R/research/tools/eventgraph/bench_gate.sh" "$HW" "${K}_bench_gen" "$RUNS/g/$N" "$(readlink -f "$GV")" "$(readlink -f "$GE")" worst 2>&1 | tail -1)
  g="gate-worst $g"
fi
echo "$K $S $md5 P=$P $od $v $ff $g"
