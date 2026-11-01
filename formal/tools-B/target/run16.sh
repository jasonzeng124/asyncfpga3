#!/usr/bin/env bash
# Shard B (UNTRUSTED): adv.py (causal paths + adversarial runs) on the 16 gcd_rig.v vectors.
# usage: run16.sh NET.json ARBS.json BND.json OUTDIR [corner] [kappa]
set -u
NET=$1; ARBS=$2; BND=$3; OUT=$4; C=${5:-0.5}; K=${6:-0.0}
HERE=$(cd "$(dirname "$0")" && pwd)
V="0,5 7,0 0xC,0x12 0x30,0x12 1,1 0x11,5 0x798F20,0x12B87CA0 0x42F,0x1CE 0x10E,0xC0 0x10000,0x1000 0x18697,0x18697 0x1E240,0xC0A14 0x7FFFFFFF,2 0xF4240,0xF423F 0x24,0x3C 0x400,0x300"
i=0; for p in $V; do
  mkdir -p "$OUT/t$i"
  ( TMPDIR="$OUT/t$i" python3 -I "$HERE/adv.py" "$NET" "$ARBS" "$BND" "$p" "$C" "$K" > "$OUT/vec$i.txt" 2>&1 ) &
  i=$((i+1)); [ $((i % 3)) = 0 ] && wait
done; wait
