#!/usr/bin/env bash
# The measurements quoted in the cell headers.  Each probe prints one number
# that a comment in rtl/ depends on; run them after changing anything timing-
# related, or the write-ups drift away from the library.
set -u
cd "$(dirname "$0")/../.."
mkdir -p build/probes
for p in verify/probes/*.v; do
    n=$(basename "$p" .v)
    echo "-- $n"
    iverilog -g2012 -gspecify -DBD_ROUTE_PS="${BD_ROUTE_PS:-0}" \
        -o "build/probes/$n.vvp" sim/bd_prims_sim.v rtl/*.v "$p" || continue
    vvp "build/probes/$n.vvp"
done
