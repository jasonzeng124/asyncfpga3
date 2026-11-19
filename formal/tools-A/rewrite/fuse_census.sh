#!/usr/bin/env bash
# fuse_census.sh FIXTURES_DIR BDC_DIR "K=V,K=V" [OUT.txt]
# fuse_check.py on every kernel FIXTURES_DIR/<k>/comp/handshake_transformed.mlir: A = default knobs, B = the given knobs
# (e.g. your ringfuse switch). One line per kernel: PROVED (Lean) / REFUSED (why) / same rules / dfimport failed.
# Example: fuse_census.sh cloud/fixtures/frontend bdc "BDC_RINGFUSE=1" ringfuse_census.txt
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
FX=$1; BDC=$2; ENVB=$3; OUT=${4:-/dev/stdout}
[ "$OUT" = /dev/stdout ] || : > "$OUT"
for d in "$FX"/*/; do
  k=$(basename "$d"); f="$d/comp/handshake_transformed.mlir"; [ -f "$f" ] || continue
  r=$(timeout 900 python3 "$HERE/fuse_check.py" "$f" "$f" --env-b "$ENVB" --bdc "$BDC" 2>&1 | grep "^fuse_check" | tail -1 | cut -c1-140)
  printf "%-28s %s\n" "$k" "${r:-dfimport failed}" >> "$OUT"
done
