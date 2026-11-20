#!/usr/bin/env bash
# draw.sh TREE RT K OUT -- one draw of research/tools/suite/suite_one.sh's judging step, with TREE's code, on the
# route $RUNS/hw/RT (share_test_2): bench_gate.sh draw:K with the C's arrays (GATE_MEMEXP), GATE_RUNTS=1 (suite_one's
# default), the prjxray SDF given in $XS (copied in, as suite_one copies $RD/xray.sdf).  The draw's work directory is
# kept (suite_one deletes it).  Writes OUT/draw_K.txt (suite_one's line) and OUT/benchres_K.txt.
set -uo pipefail
T=$(cd "$1" && pwd); RT=$2; K=$3; mkdir -p "$4"; O=$(cd "$4" && pwd)
J=/tmp/bot/sa/dsp_scratch/judge
D=share_test_2_bench_gen; V=research/data/suite/vec/share_test_2.hex
HW=$RUNS/hw/$RT; W=$RUNS/g/$RT/d$K
mkdir -p "$W"; cp "$XS" "$W/xray.sdf"
export GATE_MEMEXP=$J/memexp.txt PYTHONDONTWRITEBYTECODE=1
date -u +"start %FT%TZ" > "$O/draw_$K.time"
g=$(GATE_RUNTS=${GATE_RUNTS-1} "$T/research/tools/eventgraph/bench_gate.sh" "$HW" "$D" "$W" "$T/$V" "$J/exp.txt" "draw:$K" 2>&1 | tail -1)
date -u +"end %FT%TZ" >> "$O/draw_$K.time"
echo "draw $K $(cut -d' ' -f3-8 "$W/draw_$K.txt" 2>/dev/null) :: ${g:-none}" > "$O/draw_$K.txt"
grep '^BENCHRES' "$W/draw_$K/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$O/benchres_$K.txt"
cat "$O/draw_$K.txt"
