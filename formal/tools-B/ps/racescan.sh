#!/usr/bin/env bash
# Shard B (UNTRUSTED): racetab.py over the 16 rig + NV full-width vectors (single pair each, corner C, mid-window).
# usage: racescan.sh NET BND OUTDIR [corner] [NV]
set -u
NET=$1; BND=$2; OUT=$3; C=${4:-0.5}; NV=${5:-16}
HERE=$(cd "$(dirname "$0")" && pwd); TB=$HERE/../target; VF=$HERE/../../target/gcd_ps_vec1000.hex; mkdir -p "$OUT"
V="0,5 7,0 0xC,0x12 0x30,0x12 1,1 0x11,5 0x798F20,0x12B87CA0 0x42F,0x1CE 0x10E,0xC0 0x10000,0x1000 0x18697,0x18697 0x1E240,0xC0A14 0x7FFFFFFF,2 0xF4240,0xF423F 0x24,0x3C 0x400,0x300"
V="$V $(head -n "$NV" "$VF" | awk '{print "0x"$1",0x"$2}' | tr '\n' ' ')"
i=0; for p in $V; do
  ( python3 -I "$TB/simb.py" "$NET" "$BND" --pairs "$p" --corner "$C" --datachange broad --tmax 60000000 --dump "$OUT/d$i.json" > "$OUT/sim$i.txt" 2>&1
    python3 -I "$HERE/racetab.py" "$NET" "$OUT/d$i.json" "$OUT/rt$i.json" "$C" > "$OUT/rt$i.txt" 2>&1; rm -f "$OUT/d$i.json" ) &
  i=$((i+1)); [ $((i % 3)) = 0 ] && wait
done; wait
