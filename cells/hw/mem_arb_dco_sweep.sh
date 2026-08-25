#!/usr/bin/env bash
# mem_arb_dco_sweep.sh -- find the DCO band for the ARBITRATED memory port.
#
# DCO is the delay that makes the load station's acknowledge trail the RAM's
# read data (rule C).  Until 2026-08-24 this project had no way to measure it
# on the arbitrated port: hw/mem_arb_ps.v captured the read data through a
# synchroniser the host polled tens of ns later, so every DCO from 0 upward
# looked green.  The edge-sampled checker added that day latches z_data on the
# RAW z_req edge -- what a downstream bundled-data station actually sees -- and
# goes red at DCO=0 with 64/64 mismatches.  This script walks DCO across its
# range and asks where the transition is.
#
# THE SEED IS PINNED.  Every rebuild reseeds placement, and this project has
# measured route scatter large enough to swamp several delay links (see
# bdc/AUDIT.md section 7 and cells/verify/resize.sh).  An unpinned sweep would
# be measuring the router as much as the delay.  One pinned seed is still ONE
# SAMPLE of the route -- a band found here is the band for this placement, not
# a portable constant, and the same sweep at another seed can and should move.
#
# EXPECT NON-MONOTONE RESULTS.  bd_mem's own DCO band (cells/hw/MEM_DCO.md)
# came out non-monotone, which is why this sweeps every point instead of
# binary-searching for an edge.  A hole in the middle of a passing range is a
# result, not noise to be smoothed away.
set -u
cd "$(dirname "$0")/.."

XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
SEED=${NEXTPNR_SEED:-1}
# WHICH delay to sweep: dco (rule C, clock-to-out before the ack) or usetup
# (rule B, address+data setup into the RAM).  Both are per-RAM and both are
# swept on BOTH gangs together -- the two gangs' clocks arrive ~285 ps apart,
# so sweeping them independently would be measuring the skew, not the delay.
WHAT=${WHAT:-dco}
case "$WHAT" in
  dco)    KNOB=UCO;    FIXED="USETUP fixed at 8/8" ;;
  usetup) KNOB=USETUP; FIXED="UCO fixed at 12/12" ;;
  *) echo "WHAT must be dco or usetup"; exit 2 ;;
esac
VALUES=${*:-0 1 2 3 4 5 6 7 8 10 12}
OUT=build/hw/mem_arb_${WHAT}_sweep.txt

: > "$OUT"
echo "$WHAT sweep, seed $SEED, $FIXED" | tee -a "$OUT"
printf '%-5s %-9s %-9s %-10s %-8s %s\n' "$WHAT" p1_mism p2_mism edge_mism ns/pair verdict | tee -a "$OUT"

for D in $VALUES; do
    L="$WHAT$D"
    if ! NEXTPNR_SEED="$SEED" \
            BD_DEFINES="-DBD_SZ_UPORT_UMEM0_${KNOB}=$D -DBD_SZ_UPORT_UMEM1_${KNOB}=$D" \
            hw/build_mem.sh mem_arb_ps "$L" > "build/hw/_mem_arb_${L}.log" 2>&1; then
        printf '%-5s %s\n' "$D" "BUILD FAILED" | tee -a "$OUT"; continue
    fi
    R=$("$XSDB" hw/xsdb_mem_arb.tcl "build/hw_mem/mem_arb_ps/$L/mem_arb_ps.bit" "$L" 2>&1)
    line=$(echo "$R" | grep -o 'MEMARB .*')
    p1=$(echo "$line" | grep -o 'p1_mism=[0-9]*' | cut -d= -f2)
    p2=$(echo "$line" | grep -o 'p2_mism=[0-9]*' | cut -d= -f2)
    em=$(echo "$line" | grep -o 'edge_mism=[0-9]*' | cut -d= -f2)
    ns=$(echo "$R" | grep -o 'per-pair latency: [0-9.]*' | grep -o '[0-9.]*$')
    v="ok"; [ "${em:-x}" = "0" ] || v="RULE C RED"
    [ "${p1:-x}" = "0" ] && [ "${p2:-x}" = "0" ] || v="$v +DATA RED"
    printf '%-5s %-9s %-9s %-10s %-8s %s\n' "$D" "${p1:-?}" "${p2:-?}" "${em:-?}" "${ns:-?}" "$v" | tee -a "$OUT"
done
echo "-> $OUT"
