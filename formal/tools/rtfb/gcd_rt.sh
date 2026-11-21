#!/usr/bin/env bash
# Probe C-10f / C-10f2: RT_FB for every C-element of a routed gcd_hw (the board-measured shipped
# kernel), from its bitstream read back.  C-10f2: the routes are formal/tools/rtfb/route_gcd.sh's
# (C-10e's recipe: the project flow cells/hw/build_hw.sh gcd_hw on a private copy of cells/ and
# bdc/, cloud/fixtures/frontend/gcd, BDC_SELECT_PADS=gcd_hw_pads.json, BD_RLOC=v4, toolchain.sh
# first, NEXTPNR_SEED pinned; d = no --seed; optional NEXTPNR_FREQ).  COPIED to build/gcd/s<TAG>.
#     formal/tools/rtfb/gcd_rt.sh SEED [FREQ|-] [--lean]
# The Lean data is RtFbGcdS<SEED>.lean (no FREQ) or RtFbGcdF<FREQ>S<SEED>.lean.
set -euo pipefail
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../../.." && pwd)
S=$1; FREQ=${2:--}; [ "$FREQ" = - ] && FREQ=; TAG=$S${FREQ:+_f$FREQ}
NS=RtFbGcd${FREQ:+F$FREQ}S$S
SRC=$HERE/build/tree_$TAG/cells/build/hw/gcd_hw; BLOG=$HERE/build/route_logs/build_$TAG.log
D=$HERE/build/gcd/s$TAG; mkdir -p "$D"
grep -q "fasm_audit PASS" "$BLOG" || { echo "no fasm_audit PASS for $TAG"; exit 1; }
for f in gcd_hw.fasm gcd_hw_routed.json gcd_hw.sdf toolchain.txt pnr.log; do cp "$SRC/$f" "$D/"; done
PRJ=$TC/openxc7-src/prjxray; DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PART=xc7z010clg400-1
if grep -q "build_hw.sh PASS" "$BLOG" && [ -f "$SRC/gcd_hw.bit" ]; then
    cp "$SRC/gcd_hw.bit" "$D/"
else
    # 10e's build stopped after fasm_audit PASS (its bitstream step died): write the bits here,
    # exactly as build_hw.sh does (fasm2frames -> xc7frames2bit)
    echo "seed $S: writing the bitstream here (10e's build_hw.sh did not finish)"
    PYTHONPATH="$PRJ:$PRJ/third_party/fasm:$TC/openxc7/lib/python" python3 -W ignore "$PRJ/utils/fasm2frames.py" \
        --db-root "$DB" --part "$PART" "$D/gcd_hw.fasm" > "$D/gcd_hw.frames" 2> "$D/frames.log"
    "$TC/openxc7/bin/xc7frames2bit" --part_file "$DB/$PART/part.yaml" --part_name "$PART" \
        --frm_file "$D/gcd_hw.frames" --output_file "$D/gcd_hw.bit" > "$D/bit.log" 2>&1
fi
cp "$BLOG" "$D/build.log"
head -1 "$D/toolchain.txt"
PYTHONPATH="$PRJ:$PRJ/third_party/fasm" python3 -W ignore "$PRJ/utils/bit2fasm.py" --db-root "$DB" --part "$PART" \
    --bitread "$TC/openxc7/bin/bitread" "$D/gcd_hw.bit" > "$D/gcd_hw.fromBit.fasm" 2> "$D/bit2fasm.log"
sha256sum "$D"/gcd_hw.fasm "$D"/gcd_hw.fromBit.fasm "$D"/gcd_hw_routed.json "$D"/gcd_hw.sdf > "$D/sha.txt"
LEAN=(); [ "${3:-}" = --lean ] && LEAN=(--ns $NS --lean "$REPO/formal/lean/Formal/Timing/$NS.lean")
python3 -I "$HERE/rtfb_design.py" "$D/gcd_hw.fromBit.fasm" --routed "$D/gcd_hw_routed.json" --sdf "$D/gcd_hw.sdf" \
    --report "$D/rtd.txt" --json "$D/rtd.json" "${LEAN[@]}"
RTFB_NO_HOP=1 python3 -I "$HERE/rtfb_design.py" "$D/gcd_hw.fromBit.fasm" --routed "$D/gcd_hw_routed.json" \
    --sdf "$D/gcd_hw.sdf" --report "$D/rtd0.txt" > /dev/null   # C-10f model, before/after only
