#!/usr/bin/env bash
# tools-B/auto/kdraws.sh DIR KERNEL HEX SEED0 N [JOBS]  (shard B, UNTRUSTED simulation): research's draw K (SEED0..SEED0+N-1)
# on a decoded bench build (DIR/m from decode.sh), vectors from research's gate HEX (research/data/eventgraph/gate/*.hex,
# "a b" per line; one-operand kernels use a). Env DRAW_XBAND=lo,hi for slow-carry draws (research's DRAW_CARRY mapping);
# TMAX ps (default 4e8). Output dir DIR/d_SEED0[_x]; prints draws.py's summary line and every failing seed.
set -uo pipefail
D=$1; K=$2; HEX=$3; S0=$4; N=$5; J=${6:-4}; F=$(cd "$(dirname "$0")/../.." && pwd); O=$D/m
case $K in collatz|collatz64) PAIRS=$(awk 'NF>=1{printf "0x%s,0x%s ", $1, $1}' "$HEX");; *) PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' "$HEX");; esac
OUT=$D/d_${S0}${DRAW_XBAND:+_x}; mkdir -p "$OUT"
python3 "$F/tools/margin/draws.py" "$O/net.json" "$O/bnd.json" "$OUT" --kernel "$K" --pairs $PAIRS --draws "$N" --seed0 "$S0" \
  --jobs "$J" --routed "$O/routed.json" --tmax "${TMAX:-400000000}" ${DRAWS_EXTRA:-} > "$OUT/log.txt" 2>&1
grep -E "^draws|seed [0-9]+ (FAIL|UND|WRONG|HANG)" "$OUT/log.txt"
