#!/usr/bin/env bash
# C-8z2: regenerate the two generated data files and compare with the files on disk.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
NET="$HERE/../../Formal/Net"
T="$(mktemp -d)"; trap 'cp "$T"/*.lean "$NET"/; rm -rf "$T"' EXIT
cp "$NET/CapstoneLiveWitData.lean" "$NET/CapstoneLiveWitCexData.lean" "$T/"
python3 -I "$HERE/livesim.py" 12 18 --emit > /dev/null
python3 -I "$HERE/livesim.py" 12 18 --hold --emit > /dev/null
ok=1
for f in CapstoneLiveWitData.lean CapstoneLiveWitCexData.lean; do
  cmp -s "$T/$f" "$NET/$f" || { echo "DRIFT: $f"; ok=0; }
done
[ $ok = 1 ] && echo "check_drift: ok" || { echo "check_drift: FAIL"; exit 1; }
