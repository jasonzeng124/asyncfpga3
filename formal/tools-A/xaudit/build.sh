#!/usr/bin/env bash
# Build the native `xaudit` executable WITHOUT lake build (forbidden in this
# study): emit C for every module it needs with `lean -c` (through slot.sh)
# and link with leanc. Once the lead adds the [[lean_exe]] stanza, `lake exe
# xaudit` replaces this script.
#   formal/tools-A/xaudit/build.sh            -> $XAUDIT_OUT/xaudit
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
LEAN_DIR="$(cd "$HERE/../../lean" && pwd)"
OUT="${XAUDIT_OUT:-/tmp/xaudit}"
OL="${XAUDIT_OLEAN:-$OUT/olean}"
export XAUDIT_OLEAN="$OL"
export PATH=$HOME/.elan/bin:$PATH
mkdir -p "$OUT/c"
cd "$LEAN_DIR"
# proved dependencies (already built by lake: only C is emitted here)
DEPS="Formal/Core/Kleene Formal/Core/Lut Formal/Core/Circuit Formal/Core/Trace/Discrete Formal/Core/XSim Formal/Core/Ternary"
MINE="Formal/Core/XAudit/Design Formal/Core/XAudit/Untimed Formal/Core/XAudit/Fast Formal/Core/XAudit/Main"
# The proved dependencies are re-elaborated privately (olean + C into $OL /
# $OUT) with lake's module setup (package `formal`), so that every module
# agrees on symbol names; lake's own build tree is only read.
for m in $DEPS; do
  [ "${XAUDIT_SKIP_DEPS:-0}" = 1 ] && [ -f "$OUT/c/$(echo "$m" | tr / _).c" ] && continue
  "$HERE/lean.sh" "$m.lean" -c "$OUT/c/$(echo "$m" | tr / _).c"
done
for m in $MINE; do
  "$HERE/lean.sh" "$m.lean" -c "$OUT/c/$(echo "$m" | tr / _).c"
done
LEANC="$(dirname "$(readlink -f "$(command -v lean)")")/leanc"
[ -x "$LEANC" ] || LEANC="$(elan which lean | xargs dirname)/leanc"
"$LEANC" -O2 -o "$OUT/xaudit" "$OUT"/c/*.c
echo "[xaudit] built $OUT/xaudit"
