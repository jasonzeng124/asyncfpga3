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

run "toolchain: the installed nextpnr carries every patch in patches/" \
    ./verify/toolchain.sh
run "constants: derived, proved exhaustively, audited against rtl/" \
    python3 verify/inits.py --check-rtl
# run_sim.sh SKIPs a bench whose `// requires:` file is missing, and a skip is
# not a pass.  Generate first so the two memory benches actually run.
run "generate: the memory units the benches require" \
    ./hw/gen_mem_units.sh
run "protocol: arc-only timing" \
    ./run_sim.sh
run "protocol: routed-estimate timing (BD_ROUTE_PS=354)" \
    env BD_ROUTE_PS=354 ./run_sim.sh
# The memory generator's own gates.  Both are cheap and neither needs the
# toolchain -- and both were sitting in verify/ with nothing calling them,
# which for the second one is a real hole: three of tb_bdc_memseq's four modes
# are SUPPOSED to fail, and a negative control nobody runs is not a control.
run "memory: 36 shapes elaborate, and an out-of-range one is refused" \
    ./verify/mem_shapes.sh
run "memory: the release rule, the port's one-hot monitor, and the token chain" \
    ./verify/mem_modes.sh
run "cost: every cell synthesised alone" \
    python3 verify/lutcost.py
run "packing, placement, routing: one design, real chipdb" \
    ./flow.sh
run "bundling and matched-delay sizing, from the routed SDF" \
    python3 verify/tighten.py
run "and that the sizing gate catches a delay line that is not there" \
    ./verify/teeth.sh
# Rule E is a separate gate from tighten.py's rule D on purpose.  Rule D is a
# one-sided SCREEN -- it assumes every input launches at t=0, so it cannot see
# matched delay already upstream, and on gcd it calls 38 of 39 branches
# violations at a steer whose request really arrives around 10 ns.  Rule E
# measures from a common launch and finds a handful.  Only rule E's number is
# safe to act on, which is why only rule E emits padding.
run "rule E: the request really does arrive after its own select" \
    python3 verify/skew.py build/pnr/soak.sdf

echo
if [ $fail -eq 0 ]; then echo "ALL GATES PASS"; else echo "SOME GATES FAILED"; fi
exit $fail
