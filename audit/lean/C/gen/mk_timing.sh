#!/usr/bin/env bash
# Concatenate shard C's Timing modules verbatim (minus their import lines) into one file,
# because lake has not yet built Formal.Timing.* oleans. Usage: mk_timing.sh OUT [extra.lean]
set -e
T=/home/user/wt-formal/formal/lean/Formal/Timing
OUT=$1
{ echo "import Formal.Net.Prelim"
  for f in Semantics Checker CheckerToy; do echo "-- ==== verbatim: Formal/Timing/$f.lean (import lines removed) ===="; grep -v '^import ' $T/$f.lean; done
  if [ -n "${2:-}" ]; then cat "$2"; fi
} > "$OUT"
