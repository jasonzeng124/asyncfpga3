#!/usr/bin/env bash
# Shard B (UNTRUSTED): adv.py (closest both-from-idle request pair at each arbiter, causal paths, adversarial runs with
# each private cone at opposite window ends) on gcd_ps: the 16 rig vectors + the first NV full-width vectors.
# usage: arbsep.sh NET ARBS BND OUTDIR [corner] [kappa] [NV] [parallel]
set -u
NET=$1; ARBS=$2; BND=$3; OUT=$4; C=${5:-0.5}; K=${6:-0.0}; NV=${7:-16}; PAR=${8:-2}
HERE=$(cd "$(dirname "$0")" && pwd); TB=$HERE/../target; VF=$HERE/../../target/gcd_ps_vec1000.hex
V="0,5 7,0 0xC,0x12 0x30,0x12 1,1 0x11,5 0x798F20,0x12B87CA0 0x42F,0x1CE 0x10E,0xC0 0x10000,0x1000 0x18697,0x18697 0x1E240,0xC0A14 0x7FFFFFFF,2 0xF4240,0xF423F 0x24,0x3C 0x400,0x300"
V="$V $(head -n "$NV" "$VF" | awk '{print "0x"$1",0x"$2}' | tr '\n' ' ')"
i=0; for p in $V; do
  mkdir -p "$OUT/t$i"
  ( TMPDIR="$OUT/t$i" python3 -I "$TB/adv.py" "$NET" "$ARBS" "$BND" "$p" "$C" "$K" > "$OUT/vec$i.txt" 2>&1; rm -rf "$OUT/t$i" ) &
  i=$((i+1)); [ $((i % PAR)) = 0 ] && wait
done; wait
