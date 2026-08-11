#!/usr/bin/env bash
# Place-and-route gate: one design containing every cell, through the real
# openXC7 flow onto the real xc7z010clg400 chipdb.
#
#   ./flow.sh
#
# This is the gate the LUT-cost check cannot be: a count out of yosys says
# nothing about whether nextpnr can place a fractured LUT6_2 or route a
# combinational loop, and both are load-bearing for this library.
#
# Three things have to hold and all three are toolchain properties, not source
# properties:
#
#   the installed nextpnr-xilinx carries the split_lut6_2 packer patch.  A
#   stock build fails on the first fractured cell with "no wire found for port
#   O5" and there is no workaround in the source -- the library is simply
#   unbuildable without it.
#
#   --ignore-loops.  Every C-element and every latch in this library is a LUT
#   feedback loop.  nextpnr rejects combinational loops by default and there
#   is nothing to restructure: the loop IS the storage element.
#
#   -noclkbuf.  yosys inserts a global buffer on anything reaching a clock
#   pin, unasked, and bd_mem's manufactured edge reaches one.  Roughly two
#   nanoseconds land on a path a matched delay was sized against, and nothing
#   in simulation shows it.  The RTL marks the net clkbuf_inhibit as well;
#   both are required, neither is sufficient.
#
# What this does NOT do is size a single delay line -- but it produces the one
# input that can.  Delay sizing is a post-route pass over measured routed
# arrival times, and it tightens, never pads; verify/tighten.py is that pass,
# and the SDF written below is what it reads.
set -eu

cd "$(dirname "$0")"

TC=${TC:-/home/jayjay/dev2/lib/fpgatoolchain}
YOSYS=$TC/openxc7/bin/yosys
NEXTPNR=$TC/openxc7/bin/nextpnr-xilinx
CHIPDB=$TC/openxc7/xc7z010clg400.bin
CELLS_SIM=$TC/openxc7/share/yosys/xilinx/cells_sim.v

OUT=build/pnr
mkdir -p $OUT

for f in "$YOSYS" "$NEXTPNR" "$CHIPDB" "$CELLS_SIM"; do
    [ -e "$f" ] || { echo "missing: $f"; exit 2; }
done

# The board breaks out two PL pins and the soak top uses exactly those two.
cat > $OUT/soak.xdc <<'EOF'
set_property PACKAGE_PIN W13 [get_ports pin_in]
set_property IOSTANDARD LVCMOS33 [get_ports pin_in]
set_property PACKAGE_PIN W14 [get_ports pin_out]
set_property IOSTANDARD LVCMOS33 [get_ports pin_out]
EOF

# Measured delay lengths are OPT-IN, via BD_SIZES=<file>.  verify/resize.sh
# sets it; nothing else does.  Picking the file up automatically because it
# happened to be lying in the build directory would mean a bare ./flow.sh
# silently stopped being the placeholder build after one resize run, and the
# whole point of the gates is that you know which design you just checked.
SIZES=""
if [ -n "${BD_SIZES:-}" ]; then
    [ -f "$BD_SIZES" ] || { echo "BD_SIZES=$BD_SIZES does not exist"; exit 2; }
    cp "$BD_SIZES" "$OUT/sizes.vh"
    SIZES="-DBD_SIZES -I$OUT"
    echo "using measured delay lengths from $BD_SIZES"
else
    echo "using the placeholder delay lengths in verify/soak_top.v"
fi

echo "== synthesis =="
"$YOSYS" -p "
read_verilog -lib -specify $CELLS_SIM
read_verilog $SIZES rtl/*.v verify/soak_top.v
synth_xilinx -family xc7 -flatten -nodsp -nosrl -nolutram -nobram -noclkbuf -top soak_top
write_json $OUT/soak.json
stat
" > $OUT/synth.log 2>&1 || { echo "SYNTH FAILED"; tail -30 $OUT/synth.log; exit 1; }

# synth_xilinx prints its own statistics as well; only the last block is the
# final netlist.
last=$(grep -n '^=== soak_top ===' $OUT/synth.log | tail -1 | cut -d: -f1)
tail -n +"$last" $OUT/synth.log | grep -E "^\s+[0-9]+\s+(LUT|RAMB|IBUF|OBUF)" || true

lut_cells=$(tail -n +"$last" $OUT/synth.log \
            | grep -E "^\s+[0-9]+\s+LUT[1-6](_2)?$" \
            | awk '{s+=$1} END {print s+0}')
echo "yosys: $lut_cells LUT cells (a LUT6_2 counts once -- it is one site)"

echo
echo "== place and route =="
# --sdf is what verify/tighten.py reads: real per-net routed delays, which is
# the only place the matched-delay lengths can come from.
"$NEXTPNR" --chipdb "$CHIPDB" --xdc $OUT/soak.xdc --ignore-loops \
           --json $OUT/soak.json --write $OUT/soak_routed.json \
           --sdf $OUT/soak.sdf --fasm $OUT/soak.fasm > $OUT/pnr.log 2>&1 \
    || { echo "PNR FAILED"; tail -40 $OUT/pnr.log; exit 1; }

echo "routed."
echo

# The FASM is the netlist as the bitstream sees it, and it is the only place
# the fracturing claim can actually be checked.  prjxray writes ONE 64-bit
# xLUT.INIT per occupied LUT site: the O6 function in the upper half, the O5
# function in the lower.  So LUT.INIT lines ARE occupied sites.  If the packer
# had expanded each fractured cell into two sites the count would run well
# ahead of the cell count instead of tracking it.
#
# Do not try to match these INITs against the constants in verify/inits.py.
# The packer permutes LUT input pins freely and rewrites INIT to match, so the
# bits are a different -- equivalent -- constant.  What is checked here is the
# site count; the constants are proved exhaustively at the source, which is
# where they mean something.
lut_sites=$(grep -c "LUT\.INIT" $OUT/soak.fasm || true)
brams=$(grep -c "RAMB18" $OUT/soak.fasm || true)
echo "FASM:  $lut_sites occupied LUT sites, $brams BRAM lines"

if [ "$lut_sites" -gt $(( lut_cells + 4 )) ]; then
    echo "FAIL: $lut_sites sites for $lut_cells cells -- fractured pairs were split"
    echo "      (this is what a nextpnr without split_lut6_2 does)"
    exit 1
fi
echo "fractured pairs held one site each"

# A global buffer on the manufactured clock is the failure bd_mem's header is
# about, and it is silent in simulation.  It is not silent here.
if grep -qi "BUFGCTRL\|BUFG_" $OUT/soak.fasm; then
    echo "FAIL: a global clock buffer reached the bitstream -- check -noclkbuf"
    exit 1
fi
echo "no global clock buffer in the bitstream, as required"
echo
echo "routed SDF written to $OUT/soak.sdf -- run verify/tighten.py to size the"
echo "matched delays against it."
echo
echo "flow.sh PASS"
