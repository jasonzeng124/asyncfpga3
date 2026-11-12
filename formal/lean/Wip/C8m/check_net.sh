#!/usr/bin/env bash
# Drift check: regenerate the gcd_hw circuit network and compare with the committed module.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"; trap 'rm -rf "$T"' EXIT
python3 "$HERE/netgen.py" "$T/CapstoneNet.lean" 2>/dev/null
if cmp -s "$T/CapstoneNet.lean" "$HERE/../../Formal/Net/CapstoneNet.lean"; then echo "check_net: ok"
else echo "check_net: DRIFT (re-run netgen.py and re-check CapstoneNetChk)"; diff "$T/CapstoneNet.lean" "$HERE/../../Formal/Net/CapstoneNet.lean" | head; exit 1; fi
