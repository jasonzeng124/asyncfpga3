#!/usr/bin/env bash
# The 16 gcd_rig.v vectors (a = vec[31:0], b = vec[63:32]; vec = {g, b, a}), one pair per run (sequential env), on the decoded target netlist.
# usage: run_vec16.sh NET.json BND.json OUTDIR [extra sim.py args]
set -u
NET=$1; BND=$2; OUT=$3; shift 3
HERE=$(cd "$(dirname "$0")" && pwd)
V="0,5 7,0 0xC,0x12 0x30,0x12 1,1 0x11,5 0x798F20,0x12B87CA0 0x42F,0x1CE 0x10E,0xC0 0x10000,0x1000 0x18697,0x18697 0x1E240,0xC0A14 0x7FFFFFFF,2 0xF4240,0xF423F 0x24,0x3C 0x400,0x300"   # (a, b) = (vec[31:0], vec[63:32]) of gcd_rig.v
i=0; for p in $V; do
  ( python3 "$HERE/sim.py" "$NET" "$BND" --pairs $p --tmax 200000000 "$@" > "$OUT/vec$i.txt" 2>&1; echo "vec $i ($p): $(grep RESULT "$OUT/vec$i.txt")" ) &
  i=$((i+1)); [ $((i % 4)) = 0 ] && wait
done; wait
