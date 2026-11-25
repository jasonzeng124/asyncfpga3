#!/usr/bin/env bash
# Decode any routed build's FASM into Spec.lean's gate list (untrusted; README.md). Shard A, 2026-11-15.
#   formal/tools-A/target/make_net_fasm.sh BUILD.fasm WORKDIR [XDC]
# needs $TC (default ~/dev2/lib/fpgatoolchain) with openxc7's prjxray-db (cloud/toolchain-cache.sh fetch).
# Writes WORKDIR/{d0.json,net.json,roundtrip.txt}; the round trip must report "invented 0" and leave only
# storage/IO/clock configuration features.
set -euo pipefail
F=$1; W=$2; X=${3:-}
HERE=$(cd "$(dirname "$0")" && pwd); mkdir -p "$W"
[ -n "$X" ] || { X=$W/empty.xdc; : > "$X"; }    # the XDC only names IOB sites; bench builds have no decoded port
python3 "$HERE/decode_base.py" "$F" "$X" --json "$W/d0.json" 2>&1 | tail -1
python3 "$HERE/build_net.py" "$W/d0.json" "$F" - "$W/net.json" 2>&1 | grep "build_net:"
python3 "$HERE/roundtrip.py" "$W/net.json" "$F" > "$W/roundtrip.txt" 2>&1 || true
grep "^roundtrip:" "$W/roundtrip.txt"
md5sum "$F" "$W/net.json"
