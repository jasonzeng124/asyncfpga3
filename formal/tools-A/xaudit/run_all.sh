#!/usr/bin/env bash
# Regenerate the designs and every result in results/ with the xaudit binary $XAUDIT (default /tmp/xaudit/xaudit).
set -uo pipefail
cd "$(dirname "$0")"
X="${XAUDIT:-/tmp/xaudit/xaudit}"
python3 -I mkdesign.py designs >/dev/null
mkdir -p results
run() { out=$1; shift; "$X" "$@" > "results/$out.txt"; echo "$out: exit $? ($(grep SUMMARY "results/$out.txt"))"; }
run bd_c2_default            ../../tools/import/json/bd_c2.json --stim designs/bd_c2.stim.json
run pipe3_slow_corner        designs/pipe3.json --stim designs/pipe3.stim.json --bands designs/slow_corner.bands.json
run pipe3_holdviol_slow_corner designs/pipe3.json --stim designs/pipe3_holdviol.stim.json --bands designs/slow_corner.bands.json
run pipe3_slowfb             designs/pipe3.json --stim designs/pipe3.stim.json --bands designs/slowfb.bands.json
run pipe3_default_bands      designs/pipe3.json --stim designs/pipe3.stim.json
run ring3_slow_corner        designs/ring3.json --stim designs/ring3.stim.json --bands designs/slow_corner.bands.json
for j in ../../tools/import/json/*.json; do n=$(basename "$j" .json); "$X" "$j" > "results/cell_$n.txt"; echo "cell $n: exit $? ($(grep -c STORAGE "results/cell_$n.txt") storage)"; done
