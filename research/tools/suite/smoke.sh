#!/usr/bin/env bash
# smoke.sh KERNEL SEED FLOW VEC EXP -- one routed smoke check of a suite kernel (kernels/SUITE.md). FLOW = default|auto.
#   Build: research/data/alltable/run_default.sh's build, unchanged: cells/hw/build_bench.sh KERNEL with BD_NO_TIGHTEN=1
#   BD_SIZES=none BD_DSP=1 NEXTPNR_SEED=SEED (TARGET_MHZ default -> --freq 83), in a plain copy of cells/ bdc/
#   build/frontend under $RUNS/tree_FLOW (one tree per flow: both write cells/build/{gen,hw}/KERNEL*). FLOW=auto adds
#   BDC_AUTO=1 to build_bench.sh's environment, and its tree also gets research/tools/fifteen/pre_{dec,eq2}.py, which
#   bdc/auto.py's MLIR rewrites run (without them the rewrites are silently skipped; run_default.sh's tree has none).
#   No itercost dump or event graph (no period P: one seed is a smoke test, not a speed number).
#   Then research/tools/eventgraph/bench_gate.sh at worst (chains 0.21, CARRY4/F7F8/FF 1, rest 0.288, + M scatter) on
#   VEC / EXP (EXP from research/tools/suite/oracle.sh, i.e. from the C).
# Prints one line: KERNEL FLOW SEED sdf-md5 fmax=<MHz> luts=<n> gate <verdict>   (or KERNEL FLOW SEED BUILD FAILED ...)
set -euo pipefail
K=$1; S=$2; F=$3; VEC=$(readlink -f "$4"); EXP=$(readlink -f "$5")
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:?set RUNS}
case $F in default) AUTOENV=();; auto) AUTOENV=(BDC_AUTO=1);; *) echo "FLOW? $F"; exit 2;; esac
T=$RUNS/tree_$F; N=${K}_${F}_s$S; HW=$RUNS/hw/$N
[ -d "$T/cells" ] || { echo "smoke.sh: no tree $T (make it once, before running in parallel: see suite/run_smoke.sh)"; exit 2; }
[ -f "$T/build/frontend/$K/comp/handshake_transformed.mlir" ] || { echo "$K $F $S NO FIXTURE in $T"; exit 1; }
# build_bench.sh bounds each nextpnr attempt at PNR_TIMEOUT (default 420 s). On a shared, oversubscribed node that
# kills placements that are progressing (2026-11-17: cmpchain AUTO, HeAP placer alone 398 s at load 80-110), so a
# smoke route allows 1500 s unless the caller says otherwise.
export PNR_TIMEOUT=${PNR_TIMEOUT:-1500}
source "${TC:-$HOME/dev2/lib/fpgatoolchain}/openxc7/export.sh" > /dev/null
mkdir -p "$HW"
( cd "$T/cells" && rm -rf build/hw/${K}_bench_gen && env ${AUTOENV[@]+"${AUTOENV[@]}"} NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 \
    BD_SIZES=none ./hw/build_bench.sh "$K" ) > "$HW/build.log" 2>&1 || { echo "$K $F $S BUILD FAILED ($HW/build.log)"; exit 1; }
B=$T/cells/build/hw/${K}_bench_gen
cp "$B/${K}_bench_gen".{bit,sdf,fasm} "$B/${K}_bench_gen_routed.json" "$B/toolchain.txt" "$T/cells/build/gen/${K}_kernel_bench.v" "$HW/"
fmax=$(grep -oP "(?<=Max frequency for clock 'fclk0_bufg': )[0-9.]+" "$B/pnr.log" | tail -1 || echo NA)
luts=$(grep -c "LUT\.INIT" "$HW/${K}_bench_gen.fasm" || true)
md5=$(md5sum "$HW/${K}_bench_gen.sdf" | cut -c1-8)
# $RUNS/gatevec/K_FLOW.{hex,exp}, when present, replaces VEC / EXP: a deliberately short prefix of the kernel's vectors
# for a design bdc/simcheck.py already shows deadlocking (it ends at the first vector simcheck hangs on). Said in the
# result line.
# A hung batch runs to bench_gate.sh's TBATCH (default 1.2 ms of circuit time, ~1.5 h of wall at ~0.22 us/s). The
# suite's longest legitimate batch is 2 runs x <= 256 trips, measured <= ~31 us (countloop / sqrtsub, 256 trips, default
# flow): 200 us bounds a hang at ~15 min of wall; a prefix (its longest batch <= ~50 us) gets 80 us (~6 min).
SUB=""
if [ -f "$RUNS/gatevec/${K}_$F.hex" ]; then
  VEC=$RUNS/gatevec/${K}_$F.hex; EXP=$RUNS/gatevec/${K}_$F.exp; SUB=" (vectors: $VEC)"; GATE_TBATCH=${GATE_TBATCH:-80000}
fi
export GATE_TBATCH=${GATE_TBATCH:-200000}
# The vectors may be written while the route builds: wait for them (at most 30 min) rather than gate on nothing.
for _ in $(seq 180); do [ -s "$VEC" ] && [ -s "$EXP" ] && break; sleep 10; done
[ -s "$VEC" ] && [ -s "$EXP" ] || { echo "$K $F $S $md5 fmax=$fmax luts=$luts NO VECTORS ($VEC, $EXP)"; exit 1; }
g=$("$R/research/tools/eventgraph/bench_gate.sh" "$HW" "${K}_bench_gen" "$RUNS/g/$N" "$VEC" "$EXP" worst 2>&1 | tail -1)
echo "$K $F $S $md5 fmax=$fmax luts=$luts gate-worst $g$SUB"
