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
#   dco0     (rule C, RAM clock-to-out before the ack)  -> STAYS GREEN, AND
#            THAT IS A LIMITATION OF THIS HARNESS, NOT A RESULT.  Do not read
#            it as "rule C has margin".  The harness cannot test rule C at all,
#            for a structural reason:  mem_arb_ps captures lz_data through a
#            two-flop synchroniser into the 100 MHz PS clock domain, and the
#            host does not sample it until it has polled STATUS over AXI --
#            tens of nanoseconds after the load's z_req rose.  The RAM's real
#            clock-to-out is 2.454 ns (prjxray BRAM_L.sdf).  So the data is
#            always already there by the time anything looks, whatever DCO is
#            set to, and setting DCO to zero removes a delay that was never
#            load-bearing in this circuit.
#
#            To actually test rule C you need a consumer that reads z_data at
#            the instant z_req arrives and in the same clock domain -- i.e. a
#            second bundled-data station consuming the load's output, not a
#            memory-mapped register.  That harness does not exist yet.
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
        | grep -E "sizes read back|STATUS:|MISMATCH|phase1|phase2|RESULT|per-pair|MEMARB"
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
