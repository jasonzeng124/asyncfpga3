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
explicit=1
if [ ${#benches[@]} -eq 0 ]; then
    explicit=0
    benches=()
    for f in tb/tb_*.v; do benches+=("$(basename "$f" .v)"); done
fi

# A bench that needs more than the cell library says so itself, in its own
# header:
#
#     // requires: build/gen/gcd_kernel_bench.v
#
# one path per line, as many lines as it needs.  Those files are added to its
# compile line.  Everything undeclared is the CELL suite: rtl/*.v and nothing
# else.  Nothing is inferred from the file's NAME -- a name is not a property,
# and the pattern this replaced (*_gen|*_debug) both skipped benches that
# needed nothing and ran benches that did.
#
# A declared file that does not exist is a SKIP, not a failure: build
# artifacts are produced by hw/build_bench.sh, and their absence means that
# suite has not been built, not that the design is broken.  The skip names the
# bench and the missing path, so it can never be mistaken for a pass.  Naming a
# bench explicitly on the command line overrides this and always attempts it.
requires_of() { sed -n 's|^// *requires: *||p' "tb/$1.v" | tr -d '\r'; }

fail=0
skipped=()

for tb in "${benches[@]}"; do
    log=build/sim/$tb.log

    # Declared requirements.  A file the bench `include's itself must EXIST but
    # must NOT also reach the compile line -- iverilog would see every module in
    # it twice.  Anything else it declares is a source file it expects to be
    # compiled alongside.
    extra=()
    missing=""
    while IFS= read -r req; do
        [ -n "$req" ] || continue
        if [ ! -e "$req" ]; then missing="$req"; break; fi
        grep -q "include \"$req\"" "tb/$tb.v" || extra+=("$req")
    done < <(requires_of "$tb")

    if [ -n "$missing" ] && [ "$explicit" = 0 ]; then
        echo "SKIP  $tb   needs $missing (not built -- hw/build_bench.sh)"
        skipped+=("$tb")
        continue
    fi

    if ! iverilog -g2012 -gspecify -Wall -Wno-timescale \
            -DBD_ROUTE_PS="${BD_ROUTE_PS:-0}" \
            -o "build/sim/$tb.vvp" \
            sim/bd_prims_sim.v sim/bd_env.v rtl/*.v verify/attempts/*.v \
            ${extra[@]+"${extra[@]}"} \
            "tb/$tb.v" \
            > "$log" 2>&1; then
        echo "COMPILE FAIL  $tb   (see $log)"
        sed -n '1,20p' "$log"
        fail=1
        continue
    fi
    # A bench that HANGS is a real and expected failure here -- a bundled-data
    # handshake that never completes its return-to-zero simply stops, it does
    # not error -- so the gate must not wait forever for one.  A timeout is
    # reported as a FAIL naming the wall limit, never as a skip.
    # Capture the status directly.  `if ! cmd; then rc=$?` does NOT work: inside
    # the branch $? is the status of the negated pipeline, which is always 0, so
    # the 124 test never fires and a hang reports as an ordinary FAIL with no
    # output to explain it.
    timeout "${BD_SIM_TIMEOUT:-300}" vvp "build/sim/$tb.vvp" >> "$log" 2>&1
    rc=$?
    if [ "$rc" -eq 124 ]; then
        echo "TIMEOUT  $tb   no completion in ${BD_SIM_TIMEOUT:-300}s (see $log)"
        echo "*** killed after ${BD_SIM_TIMEOUT:-300}s: no completion" >> "$log"
        fail=1
        continue
    elif [ "$rc" -ne 0 ]; then
        echo "CRASH  $tb   vvp exited $rc (see $log)"
        echo "*** vvp exited $rc" >> "$log"
        fail=1
        continue
    fi
    if grep -q "$tb PASS" "$log"; then
        echo "PASS  $tb"
    else
        echo "FAIL  $tb   (see $log)"
        grep -E "FAIL|PROTOCOL|error" "$log" | head -20
        fail=1
    fi
done

if [ ${#skipped[@]} -gt 0 ]; then
    echo "skipped ${#skipped[@]} bench(es) whose artifacts are not built:" \
         "${skipped[*]}"
    echo "  build them with hw/build_bench.sh, or name one explicitly to force it"
fi

exit $fail
