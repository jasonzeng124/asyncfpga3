#!/usr/bin/env bash
# Drift check for C-8l: regenerate Formal/Net/CapstoneLinks.lean from bdc's Emitter and diff.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
LEAN="$HERE/../.."
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
python3 -I "$HERE/linkexport.py" -o "$TMP/CapstoneLinks.lean" 2>"$TMP/log"
if diff -q "$TMP/CapstoneLinks.lean" "$LEAN/Formal/Net/CapstoneLinks.lean" >/dev/null; then
  echo "[links] ok: CapstoneLinks.lean matches bdc's placement"; cat "$TMP/log" | head -1
else
  echo "[links] DRIFT:"; diff "$LEAN/Formal/Net/CapstoneLinks.lean" "$TMP/CapstoneLinks.lean" | head -10; exit 1
fi
