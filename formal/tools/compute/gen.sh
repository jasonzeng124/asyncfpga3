#!/usr/bin/env bash
# Regenerate (or, with --check, compare) the H_COMPUTE_FN unit netlists of gcd_hw route d
# from the committed yosys synthesis fixture. Python only.
#   formal/tools/compute/gen.sh [--check] [UNIT...]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; FORMAL="$(cd "$HERE/../.." && pwd)"
CHECK=0; [ "${1:-}" = "--check" ] && { CHECK=1; shift; }
UNITS=("$@"); [ ${#UNITS[@]} -gt 0 ] || UNITS=(uori0 uori1 ucmpi0 ucmpi1 ucmpi2 ucmpi3 ucmpi8 ucmpi10 uaddi0 ushrsi0 ushrsi1 ushrsi2 ushrsi3 ushrsi4)
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
xz -dc "$FORMAL/tools/fasm2lean3/fixture/gcd_hw_d.synth.json.xz" > "$TMP/s.json"
D="$FORMAL/lean/Formal/Gen/Compute/GcdD"; mkdir -p "$D"
rc=0
for u in "${UNITS[@]}"; do
  U="$(echo "${u:0:1}" | tr a-z A-Z)${u:1}"
  python3 "$HERE/extract.py" "$TMP/s.json" "$u" "Formal.Gen.Compute.GcdD.$U" "$TMP/$U.lean" > /dev/null
  if [ $CHECK = 1 ]; then
    cmp -s "$TMP/$U.lean" "$D/$U.lean" && echo "  $U up to date" || { echo "  DRIFT in $U"; rc=1; }
  else cp "$TMP/$U.lean" "$D/$U.lean"; echo "  wrote $U"; fi
done
exit $rc
