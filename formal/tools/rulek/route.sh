#!/usr/bin/env bash
# Probe C-10l2 (copy of tcheck/route.sh, C-10e): rebuild one gcd_hw route with the project's own flow, in a private copy
# of cells/ and bdc/ (so nothing under cells/build or build/ of the shared tree is touched).
#   formal/tools/tcheck/route.sh SEED      (SEED = d for build_hw's default, no --seed)
# Same settings as research/JOURNAL.md 21:40: BDC_SELECT_PADS=$T/cells/hw/gcd_hw_pads.json BD_RLOC=v4.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../../.." && pwd)
SEED=$1; FREQ=${NEXTPNR_FREQ:-100}; T=$HERE/build/tree_${SEED}f
# C-10l2: --freq always passed (CLAUDE.md); tree_SEEDf.  The gcd_hw paths rule K reads are
# asynchronous (unconstrained by --freq); only the readback/lap clocks see the target.
rm -rf "$T"; mkdir -p "$T/build/frontend/gcd"
cp -r "$REPO/cells" "$REPO/bdc" "$T/"; rm -rf "$T/cells/build"
cp -r "$REPO/cloud/fixtures/frontend/gcd/comp" "$T/build/frontend/gcd/"
ln -s "$REPO/patches" "$T/patches"; ln -s "$REPO/kernels" "$T/kernels"
"$REPO/cells/verify/toolchain.sh" > /dev/null
cd "$T/cells"
if [ "$SEED" = d ]; then unset NEXTPNR_SEED; else export NEXTPNR_SEED=$SEED; fi
NEXTPNR_FREQ=$FREQ BDC_SELECT_PADS=$T/cells/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw > "$HERE/build/build_${SEED}f.log" 2>&1
O=$T/cells/build/hw/gcd_hw
python3 verify/skew.py "$O/gcd_hw.sdf" > "$HERE/build/skew_${SEED}f.log" 2>&1 || true
python3 verify/tighten.py "$O/gcd_hw.sdf" --osc dhk --osc invhk > "$HERE/build/tighten_${SEED}f.log" 2>&1 || true
python3 verify/arb_fork.py "$O/gcd_hw.sdf" > "$HERE/build/arbfork_${SEED}f.log" 2>&1 || true
sha256sum "$O/gcd_hw.fasm" "$O/gcd_hw_routed.json" "$O/gcd_hw.sdf" > "$HERE/build/sha_${SEED}f.txt"
echo "route ${SEED}f done (freq $FREQ)"
