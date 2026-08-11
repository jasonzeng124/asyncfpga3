#!/usr/bin/env bash
# Every gate, in order of increasing claim.  See README.md for what each one
# does and, more importantly, does not prove.
set -u
cd "$(dirname "$0")"

fail=0
run() {
    echo
    echo "======================================================================"
    echo "== $1"
    echo "======================================================================"
    shift
    if "$@"; then :; else echo ">>> FAILED"; fail=1; fi
}

run "constants: derived, proved exhaustively, audited against rtl/" \
    python3 verify/inits.py --check-rtl
run "protocol: arc-only timing" \
    ./run_sim.sh
run "protocol: routed-estimate timing (BD_ROUTE_PS=354)" \
    env BD_ROUTE_PS=354 ./run_sim.sh
run "cost: every cell synthesised alone" \
    python3 verify/lutcost.py
run "packing, placement, routing: one design, real chipdb" \
    ./flow.sh
run "bundling and matched-delay sizing, from the routed SDF" \
    python3 verify/tighten.py
run "and that the sizing gate catches a delay line that is not there" \
    ./verify/teeth.sh

echo
if [ $fail -eq 0 ]; then echo "ALL GATES PASS"; else echo "SOME GATES FAILED"; fi
exit $fail
