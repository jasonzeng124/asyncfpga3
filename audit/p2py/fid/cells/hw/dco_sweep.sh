#!/usr/bin/env bash
# dco_sweep.sh -- find the DCO at which bd_mem's read data stops being valid
# at the ack edge, ON SILICON.
#
# Why this exists.  B3 derived DSETUP=2 / DCO=11 statically from prjxray's
# BRAM_L.sdf (t_co 2454 ps) and then reported "PASS on silicon, 0/49152".
# That pass was worthless: mem_port_ps's original checker sampled port_rdata
# on posedge aclk once a 2-FF-synchronized ack was high, i.e. at least 20 ns
# after ack really rose.  t_co is 2454 ps.  An observer eight times slower
# than the defect returns the same 0/49152 for DCO=11 and for DCO=0, so it
# could not have gone red and proved nothing about DCO.  This is the same
# shape as the -2587 ps race that passed for the same reason.
#
# mem_port_ps now carries a second checker that samples port_rdata on the RAW
# ack edge -- the claim DCO is actually responsible for, since ack MEANS the
# data lines are valid.  This script is that checker's negative control and
# its calibration in one sweep: build the same design at several DCO values,
# run each, and print both verdicts side by side.
#
# What the result means:
#
#   * The sync checker should read 0 mismatches at EVERY DCO, including 0.
#     That is the point -- it is the demonstration that the old evidence was
#     blind, not a bug to fix.
#   * The edge checker should go RED somewhere below the derived 11 and
#     CLEAN at and above it.  The crossing is a MEASURED DCO threshold, which
#     is strictly better evidence than a derived one.
#   * If the edge checker is clean even at DCO=0, it has not been shown to
#     work either.  Do not report the sweep as a pass in that case; report
#     that the edge checker's own resolution -- routed (ack -> CLK) minus
#     (port_rdata -> D) at the edge_cap flop -- is wider than t_co, and read
#     that skew out of the routed SDF before drawing any conclusion.
#
# Usage: cells/hw/dco_sweep.sh [dco ...]     (default: 0 2 4 6 8 11)
set -u

cd "$(dirname "$0")/.."

XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
DSETUP=${DSETUP:-2}
BUFG=${BUFG:-0}
LIST=${*:-0 2 4 6 8 11}
OUTDIR=build/hw_mem/dco_sweep
mkdir -p "$OUTDIR"
SUMMARY="$OUTDIR/summary.txt"
# Append, never truncate.  The threshold is only believable across seeds --
# one route is a sample -- so successive invocations at different
# NEXTPNR_SEED values have to accumulate into one table.
SEED=${NEXTPNR_SEED:-default}
{ echo; echo "# $(date -Is)  DSETUP=$DSETUP USE_BUFG=$BUFG seed=$SEED  dco: $LIST"; } >> "$SUMMARY"

for dco in $LIST; do
    tag="dco${dco}_s${SEED}"
    echo "==== DCO=$dco (DSETUP=$DSETUP USE_BUFG=$BUFG seed=$SEED) ===="
    if ! BD_DEFINES="-DBD_MEM_DSETUP=$DSETUP -DBD_MEM_DCO=$dco -DBD_MEM_USE_BUFG=$BUFG" \
         ./hw/build_mem.sh mem_port_ps "$tag" > "$OUTDIR/build_$tag.log" 2>&1; then
        echo "  BUILD FAILED -- see $OUTDIR/build_$tag.log"
        echo "dco=$dco BUILD_FAILED" >> "$SUMMARY"
        continue
    fi
    bit=$(ls build/hw_mem/mem_port_ps/$tag/*.bit 2>/dev/null | head -1)
    if [ -z "$bit" ]; then
        echo "  NO BITSTREAM -- see $OUTDIR/build_$tag.log"
        echo "dco=$dco NO_BITSTREAM" >> "$SUMMARY"
        continue
    fi
    BD_MEM_DSETUP=$DSETUP BD_MEM_DCO=$dco BD_MEM_USE_BUFG=$BUFG \
        "$XSDB" hw/xsdb_mem_port.tcl "$bit" "$tag" > "$OUTDIR/run_$tag.log" 2>&1
    rc=$?
    line=$(grep -m1 '^MEMPORT ' "$OUTDIR/run_$tag.log")
    if [ -z "$line" ]; then
        echo "  RUN PRODUCED NO VERDICT (rc=$rc) -- see $OUTDIR/run_$tag.log"
        echo "dco=$dco NO_VERDICT rc=$rc" >> "$SUMMARY"
        continue
    fi
    echo "  $line"
    echo "$line" >> "$SUMMARY"
done

echo
echo "==== sweep summary (accumulated across every invocation) ===="
cat "$SUMMARY"
echo
echo "Read it as: sync_mism is expected to be 0 everywhere -- that is the"
echo "blindness being demonstrated.  edge_mism going nonzero as DCO shrinks"
echo "is the checker proving it can go red, and the smallest DCO with"
echo "edge_mism=0 is the measured threshold.  edge_mism=0 at DCO=0 means the"
echo "edge checker is ALSO blind and nothing here is evidence yet."
