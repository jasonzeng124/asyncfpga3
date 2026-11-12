#!/usr/bin/env bash
# Probe C-11f: route the WHOLE gcd_hw with the project's own flow (cells/hw/build_hw.sh,
# as formal/tools/tcheck/route.sh does: BDC_SELECT_PADS=cells/hw/gcd_hw_pads.json, BD_RLOC=v4,
# private copy of cells/ and bdc/), plus --freq 100 (NEXTPNR_FREQ; CLAUDE.md), then make the
# .bit from nextpnr's FASM and READ IT BACK (bitread + bit2fasm), as fasm2lean2/route.sh does.
#   formal/tools/fasm2lean3/route.sh SEED     (SEED = d for build_hw's default, no --seed)
# Large outputs go to build/ (git-ignored); the small reviewable ones to fixture/.
set -euo pipefail
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../../.." && pwd)
SEED=$1; T=$HERE/build/tree_$SEED; FIX=$HERE/fixture; mkdir -p "$FIX"
rm -rf "$T"; mkdir -p "$T/build/frontend/gcd"
cp -r "$REPO/cells" "$REPO/bdc" "$T/"; rm -rf "$T/cells/build"
cp -r "$REPO/cloud/fixtures/frontend/gcd/comp" "$T/build/frontend/gcd/"
ln -s "$REPO/patches" "$T/patches"; ln -s "$REPO/kernels" "$T/kernels"
"$REPO/cells/verify/toolchain.sh" > "$HERE/build/toolchain_$SEED.txt" 2>&1 \
    || { cat "$HERE/build/toolchain_$SEED.txt"; echo "toolchain.sh FAILED: nothing routed here is a result"; exit 1; }
cd "$T/cells"
if [ "$SEED" = d ]; then unset NEXTPNR_SEED; else export NEXTPNR_SEED=$SEED; fi
export NEXTPNR_FREQ=${NEXTPNR_FREQ:-100}
BDC_SELECT_PADS=$T/cells/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw > "$HERE/build/build_$SEED.log" 2>&1 \
    || { tail -30 "$HERE/build/build_$SEED.log"; exit 1; }
O=$T/cells/build/hw/gcd_hw
B=$HERE/build/gcd_hw_$SEED
cp "$O/gcd_hw.fasm" "$B.fasm"; cp "$O/gcd_hw.json" "$B.json"; cp "$O/gcd_hw_routed.json" "$B.routed.json"
cp "$O/gcd_hw.xdc" "$B.xdc"
# the .bit, made here from nextpnr's FASM exactly as fasm2lean2/route.sh does, then read back
PRJ=$TC/openxc7-src/prjxray; DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PART=xc7z010clg400-1
PYTHONPATH="$PRJ:$PRJ/third_party/fasm:$TC/openxc7/lib/python" python3 -W ignore "$PRJ/utils/fasm2frames.py" \
    --db-root "$DB" --part "$PART" "$B.fasm" > "$B.frames" 2> "$B.frames.log"
"$TC/openxc7/bin/xc7frames2bit" --part_file "$DB/$PART/part.yaml" --part_name "$PART" \
    --frm_file "$B.frames" --output_file "$B.bit" > "$B.bit.log" 2>&1
PYTHONPATH="$PRJ:$PRJ/third_party/fasm" python3 -W ignore "$PRJ/utils/bit2fasm.py" --db-root "$DB" --part "$PART" \
    --bitread "$TC/openxc7/bin/bitread" "$B.bit" > "$B.fromBit.fasm" 2> "$B.bit2fasm.log"
# build_hw.sh's own .bit, if any, for comparison of the FASM it was made from
ls "$O"/*.bit > /dev/null 2>&1 && cp "$O"/gcd_hw.bit "$B.flow.bit" || true
grep -m1 nextpnr "$O/toolchain.txt" > "$FIX/gcd_hw_$SEED.toolchain" 2>/dev/null || true
cat "$HERE/build/toolchain_$SEED.txt" >> "$FIX/gcd_hw_$SEED.toolchain"
grep -E "fasm_audit|FASM AUDIT|audit" "$HERE/build/build_$SEED.log" | tail -3 > "$FIX/gcd_hw_$SEED.audit" || true
grep -E "Max frequency|PASS|FAIL" "$O/pnr.log" | tail -4 > "$FIX/gcd_hw_$SEED.pnr" || true
sha256sum "$B.fasm" "$B.fromBit.fasm" "$B.json" "$B.bit" | sed "s|$HERE/build/||" > "$FIX/gcd_hw_$SEED.sha256"
echo "route $SEED done: $(grep -vc '^\s*$' "$B.fromBit.fasm") features read back"
