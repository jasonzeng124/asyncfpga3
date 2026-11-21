#!/usr/bin/env bash
# pnr_direct.sh BIN INDIR OUTDIR SEED TOP [extra nextpnr args...]
# build_bench.sh's exact nextpnr call (--ignore-loops --seed S --freq 83 --timing-allow-fail) on INDIR/TOP.{json,xdc}.
set -euo pipefail
BIN=$1; IN=$2; OUT=$3; S=$4; TOP=$5; shift 5
mkdir -p "$OUT"
CHIPDB=/home/afpga/dev2/lib/fpgatoolchain/openxc7/xc7z010clg400.bin
"$BIN" --chipdb "$CHIPDB" --xdc "$IN/$TOP.xdc" --ignore-loops --seed "$S" --freq 83 --timing-allow-fail \
    --json "$IN/$TOP.json" --write "$OUT/${TOP}_routed.json" --sdf "$OUT/$TOP.sdf" --fasm "$OUT/$TOP.fasm" "$@" \
    > "$OUT/pnr.log" 2>&1 || { echo "PNR FAILED $OUT"; exit 1; }
echo "$OUT sdf $(md5sum < "$OUT/$TOP.sdf" | cut -c1-8) fasm $(md5sum < "$OUT/$TOP.fasm" | cut -c1-8) json $(md5sum < "$OUT/${TOP}_routed.json" | cut -c1-8) $(grep -o 'GND_NET: [0-9/]* sinks bridged ([0-9]* left' "$OUT/pnr.log")"
