#!/usr/bin/env bash
# Sweep RO_WIDTH at a fixed RO_DELAY: how much of a kernel stage is the latch?
#
#   hw/ro_width_sweep.sh [widths...]        default: 8 16 32
#
# WHAT THIS IS FOR.  Decomposing xorshift's measured 104.1 ns per iteration
# leaves about 5 ns per ring stage that neither the matched delay chains nor
# the protocol floor account for.  That residual is now the largest single
# term in the per-iteration cost -- larger, after fusion, than the delay lines
# themselves -- so it is worth knowing what it is rather than modelling around
# it.
#
# Three candidates, and this sweep isolates the first: the payload latch.  The
# rig carries 8 bits per stage and the kernels carry 32, and bd_latch is W/2
# LUTs, so a kernel stage's latch is four times the rig's.  If the per-stage
# slope moves with width, the latch is the answer and its size is measured
# here rather than argued.  If it does not, the latch is ruled out and the
# remaining candidates are the bd_join in each cell's request path and the
# routing between cells, which sit far apart in a kernel and adjacent here.
#
# RO_DELAY is pinned at 3 because that is the point where all five rings clear
# the counter-closure gate with the tightest fit of the whole delay sweep
# (R^2 = 0.998), so any movement in the slope is width and not the gate
# dropping a different ring at each width.
set -eu
cd "$(dirname "$0")/.."

TOP=ro_link_ps
DELAY=${RO_DELAY:-3}
SWEEP=build/hw/ro_width_sweep
mkdir -p "$SWEEP"
SUMMARY=$SWEEP/summary.txt

for w in "${@:-8 16 32}"; do
    echo "==== RO_WIDTH=$w (RO_DELAY=$DELAY) ===="
    BD_DEFINES="-DRO_DELAY=$DELAY -DRO_WIDTH=$w" NEXTPNR_FREQ=350 BD_NO_TIGHTEN=1 \
        ./hw/build_hw.sh "$TOP" > "$SWEEP/build_w$w.log" 2>&1 || {
            echo "  BUILD FAILED (see $SWEEP/build_w$w.log)"; continue; }
    grep -E "^\s+[0-9]+\s+LUT" "$SWEEP/build_w$w.log" | sed 's/^/  /'
    cp "build/hw/$TOP/pnr.log" "$SWEEP/pnr_w$w.log"
    ./hw/run_ro_link.sh "w$w" > "$SWEEP/run_w$w.log" 2>&1 || true
    grep -E "^ROLINK|RESULT VOID|=== w" "$SWEEP/run_w$w.log" | sed 's/^/  /' || true
    grep -E "^ROLINK" "$SWEEP/run_w$w.log" >> "$SUMMARY" || true
done

echo
echo "==== width sweep summary (RO_DELAY=$DELAY) ===="
cat "$SUMMARY"
echo
echo "slope_ns is nanoseconds per handshake stage.  The DIFFERENCE across"
echo "widths is the latch; a kernel stage carries 32 bits, so compare w8 to"
echo "w32 and multiply nothing.  If the slope does not move, the ~5 ns per"
echo "kernel stage is not the latch and the next suspects are the bd_join and"
echo "the routing between cells."
