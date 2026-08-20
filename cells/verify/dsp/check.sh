#!/usr/bin/env bash
# Does the toolchain SYNTHESISE a correct 32x32 multiply?
#
#     cells/verify/dsp/check.sh
#
# This exists to keep one half of the DSP48E1 finding honest.  The board gets
# wrong products out of an inferred DSP (see cells/flow.sh, and hw/mult_ps.v
# for the reproducer).  The obvious first suspect is yosys's DSP mapping, and
# this script rules it out without involving hardware at all: synthesise a
# bare `a * b` with the SAME flags the flow uses, then simulate the resulting
# netlist against Verilog's own `*` using the toolchain's own cell models.
#
# Both sides run in the same simulator on the same vectors, so a mismatch
# here would be the mapping and nothing else.  It passes -- which is why the
# fault has to be downstream of synthesis.
#
# Note the deliberate absence of -gspecify: cells_sim.v's specify blocks use
# bit-selected paths that iverilog rejects, and no timing is being measured
# here, only values.
set -euo pipefail

TC=${TC:-/home/jayjay/dev2/lib/fpgatoolchain}
CELLS=$(cd "$(dirname "$0")/../.." && pwd)
SRC=$CELLS/verify/dsp
WORK=$CELLS/build/verify/dsp
mkdir -p "$WORK"

echo "== synthesis (DSP inference forced ON) =="
"$TC/openxc7/bin/yosys" -p "
read_verilog -lib -specify $TC/openxc7/share/yosys/xilinx/cells_sim.v
read_verilog $SRC/mult32.v
synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -top mult32
write_verilog -noattr $WORK/mult32_dsp.v
" > "$WORK/yosys.log" 2>&1

N=$(grep -c 'DSP48E1' "$WORK/mult32_dsp.v" || true)
echo "   $N DSP48E1 in the netlist"
[ "$N" -gt 0 ] || { echo "no DSP inferred -- this check proves nothing"; exit 1; }

echo "== simulate the netlist against a*b =="
iverilog -g2012 -o "$WORK/tb.vvp" \
    "$TC/openxc7/share/yosys/xilinx/cells_sim.v" \
    "$WORK/mult32_dsp.v" "$SRC/tb_mult32.v" 2> >(grep -v -i warning >&2)
OUT=$(vvp "$WORK/tb.vvp")
echo "$OUT"
echo "$OUT" | grep -qE '^(directed|random): +0 of' || { echo "NETLIST IS WRONG"; exit 1; }
echo "$OUT" | grep -q 'directed: 0 of' || { echo "NETLIST IS WRONG"; exit 1; }
echo "$OUT" | grep -q 'random:   0 of' || { echo "NETLIST IS WRONG"; exit 1; }
echo "verify/dsp PASS -- synthesis is not the fault"
