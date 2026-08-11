#!/usr/bin/env bash
# Protocol simulation gate.  Runs one testbench, or all of them.
#
#   ./run_sim.sh              all benches
#   ./run_sim.sh tb_merge     one bench
#   BD_ROUTE_PS=354 ./run_sim.sh
#
# Simulation is the weakest gate in the signoff table: it drives the protocol
# perfectly and will not show a return-to-zero violation or a bundling
# failure, because both are properties of routed silicon.  A green run here
# means the logic and the handshake sequencing are right, and nothing more.
#
# verify/attempts/ is compiled in too.  Nothing there is a library cell -- it
# is recorded negative results, kept because a bench that reproduces a defect
# is the only thing that keeps the write-up true.  Unused modules cost nothing.
#
# BD_ROUTE_PS adds a per-arc routing figure to the prjxray silicon arcs the
# model is built from.  Zero, the default, is the arc-only regime: every cell
# in the library is at its most fragile there, because routing is ~74% of a
# real hop and an arc-only figure lands about three times short.  354 ps is
# the routed-hop estimate.  Both regimes must be green, and one relative
# ordering in the arbiter only holds in the second -- see tb_arb.
set -u

cd "$(dirname "$0")"
mkdir -p build/sim

benches=("$@")
if [ ${#benches[@]} -eq 0 ]; then
    benches=()
    for f in tb/tb_*.v; do benches+=("$(basename "$f" .v)"); done
fi

fail=0
for tb in "${benches[@]}"; do
    log=build/sim/$tb.log
    if ! iverilog -g2012 -gspecify -Wall -Wno-timescale \
            -DBD_ROUTE_PS="${BD_ROUTE_PS:-0}" \
            -o "build/sim/$tb.vvp" \
            sim/bd_prims_sim.v sim/bd_env.v rtl/*.v verify/attempts/*.v \
            "tb/$tb.v" \
            > "$log" 2>&1; then
        echo "COMPILE FAIL  $tb   (see $log)"
        sed -n '1,20p' "$log"
        fail=1
        continue
    fi
    vvp "build/sim/$tb.vvp" >> "$log" 2>&1
    if grep -q "$tb PASS" "$log"; then
        echo "PASS  $tb"
    else
        echo "FAIL  $tb   (see $log)"
        grep -E "FAIL|PROTOCOL|error" "$log" | head -20
        fail=1
    fi
done

exit $fail
