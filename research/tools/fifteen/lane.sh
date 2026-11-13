#!/usr/bin/env bash
# lane.sh LANE NAME KERNEL SIZES_VH SEED VECFILE [ENV...] -- one bench build + the itercost full stack + the timed event
# graph, in a private git worktree (/home/user/runs/wt/LANE, checked out at this repo's HEAD), so several lanes can
# build at once without sharing cells/build/.  The same steps as storage_pass.sh's build():
#   cells/hw/build_bench.sh with the board flags (BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0, BD_SIZES=SIZES_VH, ENV),
#   fullstack_dump.sh (bits-decoded netlist, prjxray SDF, fid, chains 0.21, CARRY4/F7F8/FF 1, rest 0.288, no scatter),
#   eventgraph.py (period, critical cycle, check against trace.py).
# Keeps: /home/user/runs/hw/NAME (bit, sdf, routed.json, kernel.v, fasm), /home/user/runs/r/NAME (run + eventgraph),
# and research/data/eventgraph/graphs/NAME (nodes/arcs/check/kernel/provenance/benchres/build.txt).
# SIZES_VH is relative to the repo root.  Prints one line: NAME sdf-md5 period odata verdict.
set -euo pipefail
L=$1; N=$2; K=$3; Z=$4; S=$5; VEC=$(readlink -f "$6"); shift 6
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/home/user/runs}
WT=$RUNS/wt/$L; HW=$RUNS/hw/$N; RD=$RUNS/r/$N; G=$R/research/data/eventgraph/graphs/$N
HEAD=$(git -C "$R" rev-parse HEAD)
exec 9> "$RUNS/wt/.$L.lock"; flock 9
if [ -d "$WT" ]; then git -C "$WT" checkout -q --detach "$HEAD"; else git -C "$R" worktree add -q --detach "$WT" "$HEAD"; fi
mkdir -p "$WT/build/frontend"; cp -rn "$R/build/frontend/"* "$WT/build/frontend/"
source "${TC:-$HOME/dev2/lib/fpgatoolchain}/openxc7/export.sh" > /dev/null
mkdir -p "$HW" "$RD"
( cd "$WT/cells" && env "$@" NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES="$WT/$Z" \
    ./hw/build_bench.sh "$K" ) > "$HW/build.log" 2>&1 || { echo "$N BUILD FAILED (see $HW/build.log)"; exit 1; }
B=$WT/cells/build/hw/${K}_bench_gen
cp "$B/${K}_bench_gen".{bit,sdf,fasm} "$B/${K}_bench_gen_routed.json" "$WT/cells/build/gen/${K}_kernel_bench.v" "$HW/"
flock 9 -u   # the worktree is free for the next build; the run reads only HW
md5=$(md5sum "$HW/${K}_bench_gen.sdf" | cut -c1-8)
ff=$(python3 "$R/research/tools/ffmux_scan.py" "$HW/${K}_bench_gen.fasm" > "$HW/ffmux.txt" 2>&1 && echo ffmux-clean || echo FFMUX-FLAG)
"$R/research/tools/eventgraph/fullstack_dump.sh" "$HW" ${K}_bench_gen "$RD" "$VEC" > "$RD/../$N.run.log" 2>&1 || true
python3 "$R/research/tools/eventgraph/eventgraph.py" "$RD" auto --rj "$HW/${K}_bench_gen_routed.json" \
    --kv "$HW/${K}_kernel_bench.v" > "$RD/eventgraph.log" 2>&1 || true
rm -f "$RD/dump.vcd" "$RD/netlist_baked.v"
mkdir -p "$G"
cp "$RD"/eventgraph/{nodes.tsv,arcs.tsv,check.txt} "$G/" 2>/dev/null || true
cp "$HW/${K}_kernel_bench.v" "$G/kernel.v"; cp "$RD/provenance.txt" "$G/" 2>/dev/null || true
grep BENCHRES "$RD/run.log" | sed 's/sig=[0-9a-f]* //' > "$G/benchres.txt" || true
echo "$N $md5 $*" > "$G/build.txt"
P=$(grep -o 'period P = [0-9]*' "$G/check.txt" 2>/dev/null | grep -o '[0-9]*$' || echo NA)
od=$(grep -o 'odata=[0-9a-f]*' "$G/benchres.txt" | sort -u | tr '\n' ' ')
v=$(grep -o 'VERDICT: [A-Z ]*' "$RD/fid/equiv.txt" 2>/dev/null | head -1 || echo "VERDICT ?")
echo "$N $md5 P=$P $od $v $ff"
