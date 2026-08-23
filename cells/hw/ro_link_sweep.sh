#!/usr/bin/env bash
# Sweep RO_DELAY on the pure-link ring rig and collect one line per point.
#
#   hw/ro_link_sweep.sh [delays...]      default: 0 1 2 4 8
#
# WHY THIS IS A SWEEP AND NOT ONE BUILD.  A single ring length gives an
# average that two very different models both predict; a single RO_DELAY does
# the same thing one axis up.  Sweeping both gives two slopes from one rig:
#
#   d(lap_ns)/d(stages)   at fixed delay  -- what a handshake stage costs
#   d(stage_ns)/d(delay)  across builds   -- what one bd_delay element costs,
#                                            which verify/converge.sh already
#                                            measures independently off the
#                                            routed chains.  Agreement there
#                                            is a free cross-check on the
#                                            whole instrument; disagreement
#                                            means one of them is wrong and
#                                            says so before either number
#                                            gets quoted.
#
# RO_DELAY=0 is expected to come back VOID -- see hw/ro_link_ps.v's header on
# why a C-element built from one LUT with feedback needs its inputs separated.
# It is swept anyway, because a defect you can still reproduce is worth more
# than a comment saying you used to be able to.
set -eu
cd "$(dirname "$0")/.."

TOP=ro_link_ps
SWEEP=build/hw/ro_link_sweep
mkdir -p "$SWEEP"
SUMMARY=$SWEEP/summary.txt

for d in "${@:-0 1 2 4 8}"; do
    echo "==== RO_DELAY=$d ===="
    BD_DEFINES="-DRO_DELAY=$d" NEXTPNR_FREQ=350 BD_NO_TIGHTEN=1 \
        ./hw/build_hw.sh "$TOP" > "$SWEEP/build_d$d.log" 2>&1 || {
            echo "  BUILD FAILED (see $SWEEP/build_d$d.log)"; continue; }
    cp "build/hw/$TOP/$TOP.bit"  "$SWEEP/${TOP}_d$d.bit"
    cp "build/hw/$TOP/pnr.log"   "$SWEEP/pnr_d$d.log"
    ./hw/run_ro_link.sh "d$d" > "$SWEEP/run_d$d.log" 2>&1 || true
    grep -E "^ROLINK|RESULT VOID|=== d" "$SWEEP/run_d$d.log" | sed 's/^/  /' || true
    grep -E "^ROLINK" "$SWEEP/run_d$d.log" >> "$SUMMARY" || true
done

echo
echo "==== sweep summary ===="
cat "$SUMMARY"
echo
echo "Read it as: census_spread is max/min mean occupancy across the five ring"
echo "lengths.  One token per ring is a moving pair whose count does not depend"
echo "on length, so census_spread must be about 1.0; anything much above that"
echo "is a ring making tokens and its slope is not a measurement.  slope_ns is"
echo "the answer -- nanoseconds per handshake stage at that RO_DELAY."
