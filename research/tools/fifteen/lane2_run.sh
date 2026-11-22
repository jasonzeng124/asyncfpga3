#!/usr/bin/env bash
# lane2_run.sh NAME KERNEL VECFILE [ENV...] -- the run half of lane2.sh on a route lane2.sh already built
# ($RUNS/hw/NAME): the itercost full stack (fullstack_dump.sh), the timed event graph, the graph files into
# research/data/eventgraph/graphs/NAME.  ENV is only recorded (build.txt).  Prints lane2.sh's line:
# NAME sdf-md5 P=.. odata.. VERDICT ffmux.  lane2.sh runs it after every build unless LANE_NORUN=1 (the sizing loop's
# intermediate routes, research/tools/auto/auto_size.sh, which runs it once on the route it keeps).
set -euo pipefail
N=$1; K=$2; VEC=$(readlink -f "$3"); shift 3
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/home/user/runs}
HW=$RUNS/hw/$N; RD=$RUNS/r/$N; G=$R/research/data/eventgraph/graphs/$N
mkdir -p "$RD"
md5=$(md5sum "$HW/${K}_bench_gen.sdf" | cut -c1-8)
ff=$(python3 "$R/research/tools/ffmux_scan.py" "$HW/${K}_bench_gen.fasm" > "$HW/ffmux.txt" 2>&1 && echo ffmux-clean || echo FFMUX-FLAG)
"$R/research/tools/eventgraph/fullstack_dump.sh" "$HW" ${K}_bench_gen "$RD" "$VEC" > "$RD/../$N.run.log" 2>&1 || true
python3 "$R/research/tools/eventgraph/eventgraph.py" "$RD" auto --rj "$HW/${K}_bench_gen_routed.json" \
    --kv "$HW/${K}_kernel_bench.v" > "$RD/eventgraph.log" 2>&1 || true
# A route whose iterations alternate has no run of equal single intervals (dot2, farm suite8 seed 2: 27849 / 28203 ps,
# "steady state too short", P=NA): the graph of two iterations (--stride 2, eval_task.sh's tse_graph does the same),
# with a window of 6 periods so that a loop of 32 trips (15 stride-2 intervals per call) fits.  P is then printed per
# iteration (the 2-iteration period / 2) with stride=2 on the line; check.txt keeps the graph's own 2-iteration period.
ST=1
if ! grep -q 'period P = [0-9]' "$RD/eventgraph/check.txt" 2>/dev/null; then
  rm -rf "$RD/eventgraph"
  python3 "$R/research/tools/eventgraph/eventgraph.py" "$RD" auto --rj "$HW/${K}_bench_gen_routed.json" \
      --kv "$HW/${K}_kernel_bench.v" --stride 2 --k 6 > "$RD/eventgraph_s2.log" 2>&1 || true
  grep -q 'period P = [0-9]' "$RD/eventgraph/check.txt" 2>/dev/null && ST=2
fi
rm -f "$RD/dump.vcd" "$RD/netlist_baked.v"
mkdir -p "$G"
cp "$RD"/eventgraph/{nodes.tsv,arcs.tsv,check.txt} "$G/" 2>/dev/null || true
cp "$HW/${K}_kernel_bench.v" "$G/kernel.v"; cp "$RD/provenance.txt" "$G/" 2>/dev/null || true
grep BENCHRES "$RD/run.log" | sed 's/sig=[0-9a-f]* //' > "$G/benchres.txt" || true
echo "$N $md5 $*" > "$G/build.txt"
P=$(grep -o 'period P = [0-9]*' "$G/check.txt" 2>/dev/null | grep -o '[0-9]*$' || echo NA)
SW=""; if [ "$ST" = 2 ] && [ "$P" != NA ]; then P=$((P / 2)); SW=" stride=2"; fi
od=$(grep -o 'odata=[0-9a-f]*' "$G/benchres.txt" | sort -u | tr '\n' ' ')
v=$(grep -o 'VERDICT: [A-Z ]*' "$RD/fid/equiv.txt" 2>/dev/null | head -1 || echo "VERDICT ?")
echo "$N $md5 P=$P $od $v $ff$SW"
