#!/usr/bin/env bash
# lane.sh LANE NAME KERNEL SIZES_VH SEED VECFILE [ENV...] -- one bench build + the itercost full stack + the timed event
# graph, in a private git worktree (/home/user/runs/wt/LANE, checked out at this repo's HEAD), so several lanes can
# build at once without sharing cells/build/.  The same steps as storage_pass.sh's build():
#   cells/hw/build_bench.sh with the board flags (BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0, BD_SIZES=SIZES_VH, ENV),
#   fullstack_dump.sh (bits-decoded netlist, prjxray SDF, fid, chains 0.21, CARRY4/F7F8/FF 1, rest 0.288, no scatter),
#   eventgraph.py (period, critical cycle, check against trace.py).
# Keeps: /home/user/runs/hw/NAME (bit, sdf, routed.json, kernel.v, fasm), /home/user/runs/r/NAME (run + eventgraph),
# and research/data/eventgraph/graphs/NAME (nodes/arcs/check/kernel/provenance/benchres/build.txt).
# SIZES_VH is relative to the repo root (or absolute), or "default" (the flow's own sizing; the sizes it chose go to HW/sizes.vh), or "none" (emit.py's estimates).  Prints one line: NAME sdf-md5 period odata verdict.
set -euo pipefail
L=$1; N=$2; K=$3; Z=$4; S=$5; VEC=$(readlink -f "$6"); shift 6
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/home/user/runs}
WT=$RUNS/wt/$L; HW=$RUNS/hw/$N; RD=$RUNS/r/$N; G=$R/research/data/eventgraph/graphs/$N
HEAD=$(git -C "$R" rev-parse HEAD)
exec 9> "$RUNS/wt/.$L.lock"; flock 9
if [ -d "$WT" ]; then git -C "$WT" checkout -q --detach "$HEAD"; else git -C "$R" worktree add -q --detach "$WT" "$HEAD"; fi
rm -rf "$WT/build/frontend"; mkdir -p "$WT/build"; cp -r "$R/build/frontend" "$WT/build/"
[ -n "${MLIR_OVERRIDE:-}" ] && cp "$R/$MLIR_OVERRIDE" "$WT/build/frontend/$K/comp/handshake_transformed.mlir"
source "${TC:-$HOME/dev2/lib/fpgatoolchain}/openxc7/export.sh" > /dev/null
mkdir -p "$HW" "$RD"
if [ "$Z" = default ]; then   # SIZES_VH "default": build_bench.sh's own default sizing (MODE=tighten: hw/tighten_loop.sh)
  ( cd "$WT/cells" && rm -rf build/tighten_loop/$K build/gen/${K}_bench_gen_sizes.vh && env "$@" NEXTPNR_SEED=$S BD_DSP=1 \
      ./hw/build_bench.sh "$K" ) > "$HW/build.log" 2>&1 || { echo "$N BUILD FAILED (see $HW/build.log)"; exit 1; }
  cp "$WT/cells/build/gen/${K}_bench_gen_sizes.vh" "$HW/sizes.vh" 2>/dev/null || : > "$HW/sizes.vh"
elif [ "$Z" = none ]; then   # SIZES_VH "none": every matched delay at bdc/emit.py's own estimate (research/data/alltable)
  ( cd "$WT/cells" && env "$@" NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES=none \
      ./hw/build_bench.sh "$K" ) > "$HW/build.log" 2>&1 || { echo "$N BUILD FAILED (see $HW/build.log)"; exit 1; }
  : > "$HW/sizes.vh"
else
case $Z in /*) ZP=$Z;; *) ZP=$WT/$Z;; esac   # an absolute SIZES_VH is used in place (local sizing loops)
( cd "$WT/cells" && env "$@" NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES="$ZP" \
    ./hw/build_bench.sh "$K" ) > "$HW/build.log" 2>&1 || { echo "$N BUILD FAILED (see $HW/build.log)"; exit 1; }
fi
B=$WT/cells/build/hw/${K}_bench_gen
cp "$B/${K}_bench_gen".{bit,sdf,fasm} "$B/${K}_bench_gen_routed.json" "$WT/cells/build/gen/${K}_kernel_bench.v" "$HW/"
flock -u 9   # the worktree is free for the next build; the run reads only HW
if [ "${LANE_NORUN:-0}" = 1 ]; then   # no full stack: only the prjxray SDF that corner_audit reads (auto_size.sh's
  # intermediate routes; lane2_run.sh runs the full stack on the route the loop keeps)
  md5=$(md5sum "$HW/${K}_bench_gen.sdf" | cut -c1-8)
  ff=$(python3 "$R/research/tools/ffmux_scan.py" "$HW/${K}_bench_gen.fasm" > "$HW/ffmux.txt" 2>&1 && echo ffmux-clean || echo FFMUX-FLAG)
  PYTHONPATH=${TC:-$HOME/dev2/lib/fpgatoolchain}/openxc7-src/prjxray python3 "$R/cells/gls/fid/xray_delay.py" \
      --routed "$HW/${K}_bench_gen_routed.json" --sdf "$HW/${K}_bench_gen.sdf" --out "$RD/xray.sdf" > "$RD/xray.log" 2>&1
  echo "$N $md5 P=NORUN $ff"; exit 0
fi
exec "$R/research/tools/fifteen/lane2_run.sh" "$N" "$K" "$VEC" "$@"
