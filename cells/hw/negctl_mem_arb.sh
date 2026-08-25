#!/usr/bin/env bash
# negctl_mem_arb.sh -- the two negative controls for hw/mem_arb_ps.v.
#
# A harness that reports PASS is worth nothing until you have made it report
# FAIL on purpose.  These two builds break one delay each, at the source, and
# ask the board what happens.
#
#   hw/negctl_mem_arb.sh            # both controls
#   hw/negctl_mem_arb.sh dsetup0    # just the one that works
#
# WHAT THE TWO CONTROLS ACTUALLY ESTABLISH -- and they are NOT symmetric:
#
#   dsetup0  (rule B, address/data setup into the RAM)  -> GOES RED.  Measured
#            2026-08-24: 64/64 addresses mismatched, got=0x00000000 against
#            expect=0xc0d00a00, failing address logged in P1_FAIL_*.  The write
#            request reaches the RAM's clock before the payload reaches its
#            D pins, so the RAM latches nothing and every later load reads the
#            uninitialised cell.  This is the control that gives the PASS its
#            meaning: the harness demonstrably has the power to fail.
#
#   dco0     (rule C, RAM clock-to-out before the ack)  -> GOES RED on the
#            EDGE-SAMPLED checker only.  Measured 2026-08-24: edge_mism=64,
#            got=0xbf2f0a00 vs expect=0xc0d00a00, while P1/P2_MISMATCH stayed
#            0.  Low half right, high half garbage -- the later of the two
#            RAMB18E1 gangs misses the capture edge, which is what clock-to-out
#            failure looks like from outside.  It also runs 150.0 ns/pair
#            against 170.0, so the broken build is the fast one.
#
#            UNTIL 2026-08-24 THIS CONTROL WAS GREEN, and that was a property
#            of the harness, not of the circuit: the only consumer of the read
#            data was a synchroniser the host polled tens of ns later, so the
#            RAM's 2454 ps clock-to-out was satisfied whatever DCO was set to.
#            Fixed by adding a consumer that latches z_data on the raw z_req
#            edge the way a downstream bundled-data station does.  If you find
#            yourself with a green negative control, suspect the observer
#            before you credit the margin.
#
# Rebuilds from scratch each time (PnR is reseeded), so the routes differ from
# the reference build; see cells/verify/resize.sh and the seed discussion in
# bdc/AUDIT.md section 7 for why one route is a sample.
set -u
cd "$(dirname "$0")/.."

XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
WHICH=${1:-all}

run_one() {
    local L=$1 D=$2
    echo "=================== $L ($D) ==================="
    if ! BD_DEFINES="$D" hw/build_mem.sh mem_arb_ps "$L" > "build/hw/_mem_arb_${L}.log" 2>&1; then
        echo "$L: BUILD FAILED"; tail -5 "build/hw/_mem_arb_${L}.log"; return 1
    fi
    "$XSDB" hw/xsdb_mem_arb.tcl "build/hw_mem/mem_arb_ps/$L/mem_arb_ps.bit" "$L" 2>&1 \
        | grep -E "sizes read back|STATUS:|MISMATCH|phase1|phase2|edge-sampled|first:|RESULT|per-pair|MEMARB"
}

case "$WHICH" in
  dsetup0) run_one negctl-dsetup0 "-DBD_SZ_UPORT_UMEM0_USETUP=0 -DBD_SZ_UPORT_UMEM1_USETUP=0" ;;
  dco0)    run_one negctl-dco0    "-DBD_SZ_UPORT_UMEM0_UCO=0 -DBD_SZ_UPORT_UMEM1_UCO=0" ;;
  all)
    run_one negctl-dsetup0 "-DBD_SZ_UPORT_UMEM0_USETUP=0 -DBD_SZ_UPORT_UMEM1_USETUP=0"
    run_one negctl-dco0    "-DBD_SZ_UPORT_UMEM0_UCO=0 -DBD_SZ_UPORT_UMEM1_UCO=0"
    echo
    echo "REMINDER: dsetup0 going red is the result.  dco0 staying green is not"
    echo "a result -- this harness cannot observe rule C.  See the header."
    ;;
  *) echo "usage: negctl_mem_arb.sh [all|dsetup0|dco0]"; exit 2 ;;
esac
