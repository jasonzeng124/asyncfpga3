#!/usr/bin/env bash
# Decode the target into Spec.lean's gate list and name its boundary (all untrusted; see README.md).
#   formal/tools-A/target/make_net.sh WORKDIR     (needs the toolchain's prjxray-db and the target's files)
set -euo pipefail
W=$1; mkdir -p "$W"
HERE=$(cd "$(dirname "$0")" && pwd); T=$HERE/../../target
xz -dc "$T/gcd_hw_03e82630.fromBit.fasm.xz" > "$W/fromBit.fasm"
# the XDC only names IOB sites (2 LEDs); the target's is cells/hw's gcd_hw constraints as built
python3 "$HERE/decode_base.py" "$W/fromBit.fasm" "${XDC:?set XDC to the build's gcd_hw.xdc}" --json "$W/d0.json"
python3 "$HERE/build_net.py" "$W/d0.json" "$W/fromBit.fasm" - "$W/net.json"
python3 "$HERE/roundtrip.py" "$W/net.json" "$W/fromBit.fasm" | tee "$W/roundtrip.txt"
xz -dc "$T/gcd_hw_03e82630.json.xz" > "$W/synth.json"
python3 "$HERE/boundary.py" "$W/synth.json" "${ROUTED:?set ROUTED to the build's gcd_hw_routed.json}" "$W/net.json" "$W/bnd.json"
md5sum "$W/net.json" "$W/bnd.json"
