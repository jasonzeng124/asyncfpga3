#!/usr/bin/env bash
# Probe C-10f2: rebuild one gcd_hw route with the project's own flow, in a private copy of
# cells/ and bdc/ under formal/tools/rtfb/build/ (a copy of C-10e's formal/tools/tcheck/route.sh,
# whose build/ belongs to probe 10m this session; same recipe, so the same placement/route
# for the same toolchain and sources).  Settings as research/JOURNAL.md 21:40:
# BDC_SELECT_PADS=$T/cells/hw/gcd_hw_pads.json BD_RLOC=v4, --freq from build_hw.sh (100).
#   formal/tools/rtfb/route_gcd.sh SEED [FREQ]   (SEED = d for build_hw's default, no --seed)
# Without FREQ: C-10e/C-10f's recipe exactly (BOARD-QUEUE #1's command: build_hw.sh passes no
# --freq, nextpnr's 12 MHz default) -- needed to re-check C-10f's numbers on the SAME routes
# (FASM sha256 compared with C-10f's table).  With FREQ (e.g. 100): NEXTPNR_FREQ=FREQ, i.e.
# --freq FREQ --timing-allow-fail (CLAUDE.md), into build/tree_<SEED>_f<FREQ>.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../../.." && pwd)
SEED=$1; FREQ=${2:-}; TAG=$SEED${FREQ:+_f$FREQ}
T=$HERE/build/tree_$TAG; L=$HERE/build/route_logs; mkdir -p "$L"
rm -rf "$T"; mkdir -p "$T/build/frontend/gcd"
cp -r "$REPO/cells" "$REPO/bdc" "$T/"; rm -rf "$T/cells/build"
cp -r "$REPO/cloud/fixtures/frontend/gcd/comp" "$T/build/frontend/gcd/"
ln -s "$REPO/patches" "$T/patches"; ln -s "$REPO/kernels" "$T/kernels"
"$REPO/cells/verify/toolchain.sh" > "$L/toolchain_$TAG.txt" \
    || { cat "$L/toolchain_$TAG.txt"; echo "toolchain.sh FAILED: nothing routed here is a result"; exit 1; }
cd "$T/cells"
if [ "$SEED" = d ]; then unset NEXTPNR_SEED; else export NEXTPNR_SEED=$SEED; fi
if [ -n "$FREQ" ]; then export NEXTPNR_FREQ=$FREQ; else unset NEXTPNR_FREQ; fi
BDC_SELECT_PADS=$T/cells/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw > "$L/build_$TAG.log" 2>&1 || true
O=$T/cells/build/hw/gcd_hw
sha256sum "$O/gcd_hw.fasm" "$O/gcd_hw_routed.json" "$O/gcd_hw.sdf" > "$L/sha_$TAG.txt"
echo "route $TAG done: $(grep -c 'fasm_audit PASS' "$L/build_$TAG.log") fasm_audit PASS, $(grep -c 'build_hw.sh PASS' "$L/build_$TAG.log") build_hw PASS"
