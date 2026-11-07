#!/usr/bin/env bash
# Does the bench read the kernel's result inside its valid window?
#
#     cells/verify/bench_window.sh          (~3 min: two RTL simulations)
#
# Regression test for the August 2026 isprime readback: SIG and ODATA were
# folded from o_data_capture, a free-running mirror read in S_NEXT -- after
# bench_o_ack, when four-phase bundled data no longer promises the bus.  Five
# kernels happened to hold their output bus and passed; isprime's did not and
# read 0x80000000 on silicon.  RTL simulation never saw it because the RTL
# kernel holds its bus too.  The fix (gen_bench.py) captures result_hold in
# S_WAIT_RES, on the last edge before the acknowledge.
#
# tb_gcd_bench_gen now drives out0_data to X outside [out0_req rise,
# out0_ack rise), so the bench itself enforces the window.  This runs it on
# the generated harness (must PASS) and on a copy with the August read put
# back (SIG and ODATA from o_data_capture), which must FAIL.
set -uo pipefail
cd "$(dirname "$0")/.."

W=build/verify/bench_window
mkdir -p "$W" build/gen build/sim
python3 ../bdc/emit.py ../build/frontend/gcd/comp/handshake_transformed.mlir --no-top \
    -o build/gen/gcd_kernel_bench.v > "$W/gen.log" 2>&1 &&
python3 hw/gen_bench.py gcd --top gcd_bench_gen -o build/gen/gcd_bench_gen.v >> "$W/gen.log" 2>&1 \
    || { echo "GENERATE FAILED"; cat "$W/gen.log"; exit 1; }

python3 - build/gen/gcd_bench_gen.v "$W/late.v" <<'EOF' || exit 1
import sys
s = open(sys.argv[1]).read()
for old, new in (("sig <= {sig[30:0], sig[31]} ^ result_hold;",
                  "sig <= {sig[30:0], sig[31]} ^ o_data_capture;"),
                 ("7'h04: rdata_r = hold_valid ? result_hold : o_data_capture;",
                  "7'h04: rdata_r = o_data_capture;")):
    if s.count(old) != 1:
        sys.exit("bench_window: gen_bench.py changed; the August read cannot be re-applied (%r)" % old)
    s = s.replace(old, new)
open(sys.argv[2], "w").write(s)
EOF
sed "s|^\`include \"build/gen/gcd_bench_gen.v\"|\`include \"$W/late.v\"|" \
    tb/tb_gcd_bench_gen.v > "$W/tb_late.v"

echo "== the generated harness =="
./run_sim.sh tb_gcd_bench_gen || { echo "verify/bench_window FAIL"; exit 1; }

echo "== negative control: SIG/ODATA read after the acknowledge (the August form) =="
iverilog -g2012 -gspecify -Wno-timescale -DBD_ROUTE_PS=0 -o "$W/late.vvp" \
    sim/bd_prims_sim.v sim/bd_env.v rtl/*.v verify/attempts/*.v sim/ps7_stub.v \
    build/gen/gcd_kernel_bench.v "$W/tb_late.v" > "$W/late.compile.log" 2>&1 \
    || { echo "COMPILE FAILED"; head "$W/late.compile.log"; exit 1; }
timeout "${BD_SIM_TIMEOUT:-900}" vvp -n "$W/late.vvp" > "$W/late.log" 2>&1
rm -f "${W:?}/late.vvp"
if grep -q 'FAIL  FIXED batch: SIG matches' "$W/late.log"; then
    echo "  caught: $(grep -c '^\s*FAIL ' "$W/late.log") check(s) fail, SIG among them"
    echo "verify/bench_window PASS"
else
    echo "verify/bench_window FAIL: the bench did not see a result read after its acknowledge"
    exit 1
fi
