#!/usr/bin/env bash
# Simulate the bench harness AS YOSYS BUILT IT, not as it is written.
#
#     cells/verify/harness_pss.sh            (~3 min: one synth, two sims)
#
# The August 2026 histogram bug: gen_bench.py's hist[] read written as a
# synchronous read inside the write's clocked block made yosys infer a memory
# whose increments read 0 and wrote 1 -- on the board every bucket of batches
# of n = 1, 2, 3, 10, 100 held exactly 1 -- while RTL simulation passed the
# whole time, because iverilog simulates the RTL and never sees the inference
# (CLAUDE.md: "iverilog cannot see yosys memory inference").
#
# This synthesises the generated gcd harness (gcd_bench_gen_bridge) with the
# flags build_bench.sh uses, the kernel and the cell library left as
# black boxes so they stay RTL with their delays, and runs the unmodified
# tb_gcd_bench_gen against the harness NETLIST.  Its section 5 asserts
# sum(hist) == runs over a 64-run UNIFORM batch, an oracle the August bug
# fails.
#
# What it could and could not show, measured 2026-10-26 on yosys 0.62:
#   - re-introducing the August form (hist_rd <= hist[bucket_q] in the write's
#     block) does NOT fail: yosys 0.62 builds it correctly, in a reduced
#     module and in the full harness alike.  The August yosys did not, and
#     no copy of it is here.  So this is a guard for the CLASS (any yosys
#     inference that disagrees with the RTL anywhere in the harness), not a
#     reproduction of that bug.
#   - the negative control (--negctl, run every time) puts the August
#     SYMPTOM into the netlist -- hist_rd's flops loaded with 0, so every
#     increment writes 1 -- and section 5 must then fail.  It does
#     (hist_total=6 of 64).
#   - one section-6 check ("illegal sticky: records ill_prev_oack == 1")
#     forces internal nets by hierarchical name, which a flattened netlist
#     does not keep one-to-one; it is excluded here and only here.
set -uo pipefail
cd "$(dirname "$0")/.."

TC=${TC:-/home/jayjay/dev2/lib/fpgatoolchain}
CELLS_SIM=$TC/openxc7/share/yosys/xilinx/cells_sim.v
W=build/verify/harness_pss
mkdir -p "$W" build/gen
EXCLUDE='illegal sticky: records ill_prev_oack == 1'

python3 ../bdc/emit.py ../build/frontend/gcd/comp/handshake_transformed.mlir --no-top \
    -o build/gen/gcd_kernel_bench.v > "$W/gen.log" 2>&1 &&
python3 hw/gen_bench.py gcd --top gcd_bench_gen -o build/gen/gcd_bench_gen.v >> "$W/gen.log" 2>&1 \
    || { echo "GENERATE FAILED"; cat "$W/gen.log"; exit 1; }

DSPOPT="-nodsp"
[ "${BD_DSP:-1}" = "1" ] && DSPOPT=""
"$TC/openxc7/bin/yosys" -q -l "$W/yosys.log" -p "
read_verilog -lib -specify $CELLS_SIM
read_verilog -lib build/gen/gcd_kernel_bench.v
read_verilog -lib rtl/*.v
read_verilog build/gen/gcd_bench_gen.v
hierarchy -top gcd_bench_gen_bridge
synth_xilinx -family xc7 -flatten $DSPOPT -nosrl -nolutram -nobram -noclkbuf -top gcd_bench_gen_bridge
write_verilog -noattr $W/harness.v
" > /dev/null 2>&1 || { echo "SYNTH FAILED"; tail -20 "$W/yosys.log"; exit 1; }

# The netlist's yosys primitives, minus the ones sim/bd_prims_sim.v already
# models (LUTs; the kernel needs those with their delays).  Specify blocks
# dropped: values, not timing, are what is being checked.
python3 - "$CELLS_SIM" "$W/harness.v" "$W/cells_subset.v" <<'EOF' || exit 1
import re, sys
src = open(sys.argv[1]).read()
used = set(re.findall(r"^\s*([A-Z][A-Z0-9_]*)\s+(?:#\(|\\?\S+\s*\()", open(sys.argv[2]).read(), re.M))
used -= {"LUT1", "LUT2", "LUT3", "LUT4", "LUT5", "LUT6", "LUT6_2", "BUFG", "RAMB18E1"}
mods = {m.group(1): re.sub(r"specify.*?endspecify", "", m.group(0), flags=re.S)
        for m in re.finditer(r"^module\s+(\w+)\b.*?^endmodule", src, re.M | re.S)}
missing = sorted(u for u in used if u not in mods)
if missing:
    sys.exit("no simulation model for %s" % missing)
open(sys.argv[3], "w").write("".join(mods[u] + "\n" for u in sorted(used)))
EOF

# The netlist replaces the bench's `include of the RTL harness.
sed 's|^`include "build/gen/gcd_bench_gen.v"|// harness: the post-synthesis netlist|' \
    tb/tb_gcd_bench_gen.v > "$W/tb.v"

run() {   # run <netlist> <tag>  -> leaves $W/<tag>.log
    iverilog -g2012 -gspecify -Wno-timescale -DBD_ROUTE_PS=0 -o "$W/$2.vvp" \
        sim/bd_prims_sim.v sim/bd_env.v rtl/*.v verify/attempts/*.v sim/ps7_stub.v \
        build/gen/gcd_kernel_bench.v "$W/cells_subset.v" "$1" "$W/tb.v" \
        > "$W/$2.compile.log" 2>&1 || { echo "COMPILE FAILED ($2)"; head "$W/$2.compile.log"; return 2; }
    timeout "${BD_SIM_TIMEOUT:-900}" vvp -n "$W/$2.vvp" > "$W/$2.log" 2>&1
    rm -f "${W:?}/$2.vvp"
}
verdict() {   # failures other than the excluded one, and whether the bench finished
    grep -E '^\s*FAIL ' "$W/$1.log" | grep -vF "$EXCLUDE"
    grep -q 'tb_gcd_bench_gen \(PASS\|FAIL (\)' "$W/$1.log" || echo "  (bench did not finish)"
}

echo "== the harness as synthesised =="
run "$W/harness.v" synth || exit 1
bad=$(verdict synth)
[ -z "$bad" ] || { echo "$bad"; echo "verify/harness_pss FAIL: the netlist is not the RTL"; exit 1; }
echo "  $(grep -c '^\s*PASS ' "$W/synth.log") checks pass on the netlist (section 6's forced-name check excluded)"

echo "== negative control: hist_rd's flops loaded with 0 (the August symptom) =="
python3 - "$W/harness.v" "$W/harness_negctl.v" <<'EOF' || exit 1
import re, sys
s = open(sys.argv[1]).read()
s, n = re.subn(r"FD[CPR]E #\([^;]*?\.Q\(hist_rd\[\d+\]\)\s*\);",
               lambda m: re.sub(r"\.D\([^)]*\)", ".D(1'h0)", m.group(0)), s, flags=re.S)
if n != 16:
    sys.exit("negctl: expected 16 hist_rd flops, found %d -- the control would not be the bug" % n)
open(sys.argv[2], "w").write(s)
EOF
run "$W/harness_negctl.v" negctl
if verdict negctl | grep -q 'histogram buckets == run count'; then
    echo "  caught: $(grep -A1 'histogram buckets' "$W/negctl.log" | grep hist_total | xargs)"
else
    echo "verify/harness_pss FAIL: the histogram oracle did not see a harness whose increments read 0"
    exit 1
fi
echo "verify/harness_pss PASS -- the synthesised harness behaves as its RTL, and the oracle can tell when it does not"
