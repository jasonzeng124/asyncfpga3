#!/usr/bin/env bash
# Shard B (UNTRUSTED): storage-node race scan on gcd_ps. For each vector: baseline sim dump (simb.py, corner C,
# mid-window, sequential env), then kstar.py (static κ* per storage node) and fbscan.py (episode/loop ratios).
# usage: kscan.sh NET.json BND.json OUTDIR [corner] [nvec1000]
set -u
NET=$1; BND=$2; OUT=$3; C=${4:-0.5}; NV=${5:-16}
HERE=$(cd "$(dirname "$0")" && pwd); TB=$HERE/../target; VF=$HERE/../../target/gcd_ps_vec1000.hex
mkdir -p "$OUT"
V="0,5 7,0 0xC,0x12 0x30,0x12 1,1 0x11,5 0x798F20,0x12B87CA0 0x42F,0x1CE 0x10E,0xC0 0x10000,0x1000 0x18697,0x18697 0x1E240,0xC0A14 0x7FFFFFFF,2 0xF4240,0xF423F 0x24,0x3C 0x400,0x300"
V="$V $(head -n "$NV" "$VF" | awk '{print "0x"$1",0x"$2}' | tr '\n' ' ')"
i=0; for p in $V; do
  ( python3 -I "$TB/simb.py" "$NET" "$BND" --pairs "$p" --corner "$C" --tmax 60000000 --dump "$OUT/d$i.json" > "$OUT/sim$i.txt" 2>&1
    python3 -I "$TB/kstar.py" "$NET" "$OUT/d$i.json" "$C" 1.0 > "$OUT/k$i.txt" 2>&1
    python3 -I "$TB/fbscan.py" "$NET" "$OUT/d$i.json" "$C" 0.5 25000 2>/dev/null | head -4 > "$OUT/f$i.txt"
    rm -f "$OUT/d$i.json"; echo "$i $p $(grep RESULT "$OUT/sim$i.txt")" >> "$OUT/index.txt" ) &
  i=$((i+1)); [ $((i % 3)) = 0 ] && wait
done; wait
