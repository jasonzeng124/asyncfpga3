#!/usr/bin/env bash
# Copy the PROVED checker modules verbatim from formal/lean (read-only there) into this
# package, or with --check only verify that the copies have not drifted (exit 1 if any differ).
#   formal/tools/tcheck/sync.sh [--check]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); SRC=$HERE/../../lean
MODS="Formal/Net/Prelim.lean Formal/Timing/Semantics.lean Formal/Timing/Checker.lean Formal/Timing/WinArray.lean Formal/Timing/Unroll.lean"
rc=0
for m in $MODS; do
  if [ "${1:-}" = --check ]; then
    if cmp -s "$SRC/$m" "$HERE/$m"; then echo "  same   $m ($(sha256sum < "$HERE/$m" | cut -c1-12))"
    else echo "  DRIFT  $m: formal/lean's copy differs from the one tcheck is built from"; rc=1; fi
  else mkdir -p "$(dirname "$HERE/$m")"; cp "$SRC/$m" "$HERE/$m"; fi
done
exit $rc
