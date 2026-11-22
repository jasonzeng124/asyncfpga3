#!/usr/bin/env bash
# emit_one.sh K OUT -- bdc/auto.py + BDC_AUTO=1 bdc/emit.py --no-top for fixture build/frontend/K (as auto_size.sh's
# iteration 0 does), into OUT/K/; prints one line: K OK muxn_modules= muxn_insts= bd_mux_insts= <type:instance ...>, or
# K EMITFAIL <last log line>.  All fixtures, 3 at a time: ls build/frontend | xargs -P 3 -I{} emit_one.sh {} OUT
R=$(cd "$(dirname "$0")/../../../.." && pwd); K=$1; mkdir -p "$2/$K"; O=$(cd "$2/$K" && pwd)
f=$R/build/frontend/$K/comp/handshake_transformed.mlir
[ -f "$f" ] || { echo "$K NOFIXTURE"; exit 0; }
cd "$R"
if python3 bdc/auto.py "$f" "$O/auto.mlir" > "$O/auto.log" 2>&1 && BDC_AUTO=1 python3 bdc/emit.py "$O/auto.mlir" --no-top -o "$O/kernel.v" >> "$O/auto.log" 2>&1; then
  n=$(grep -c '^module bdc_muxn' "$O/kernel.v"); i=$(grep -cE '^\s*bdc_muxn[0-9]+_[0-9]+ ' "$O/kernel.v"); b=$(grep -cE '^\s*bd_mux ' "$O/kernel.v")
  echo "$K OK muxn_modules=$n muxn_insts=$i bd_mux_insts=$b $(grep -oE '^\s*bdc_muxn[0-9]+_[0-9]+ #\(\.DELAY\([^)]*\)\) \w+' "$O/kernel.v" | awk '{print $1":"$NF}' | tr '\n' ' ')"
else
  echo "$K EMITFAIL $(tail -1 "$O/auto.log")"
fi
