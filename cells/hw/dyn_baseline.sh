#!/usr/bin/env bash
# Place and route Dynamatic's own output for a kernel, on OUR part with OUR
# toolchain, and report the period it closes at.
#
#   hw/dyn_baseline.sh xorshift
#
# WHY THIS EXISTS.  Comparing our per-iteration cost against Dynamatic was
# blocked for a while on the belief that export-rtl emits VHDL whatever you
# ask for.  It does not.  It emits exactly the HDL its RTL CONFIG names, and
# the config is a POSITIONAL argument: pass rtl-config-verilog.json and every
# file lands as .v.  The real obstacle was smaller and duller -- export-rtl
# looks for its component generators under <dynamatic-path>/bin/generators
# while the build puts them in build/bin.  Rather than reshape the vendored
# tree, which is consumed as data and never edited, this builds a shadow
# directory of symlinks in the right shape and points --dynamatic-path at it.
#
# WHAT THE NUMBER MEANS.  Dynamatic's buffer placement puts one
# ONE_SLOT_BREAK_DV (DV_LATENCY 1) and one ONE_SLOT_BREAK_R (DV_LATENCY 0) on
# each ring, so forward latency is ONE CYCLE per iteration -- printed below
# from hw.mlir's own buffer parameters rather than assumed.  Their
# per-iteration cost is therefore just their clock period, and the only honest
# way to get that is to route their netlist on the same silicon we quote our
# own numbers on.
#
# The wrapper is I/O-bound on purpose: a kernel this size has far more ports
# than the part has pins, so inputs come from registers and outputs collapse
# to one.  Nothing in it touches the kernel's own paths, so the period nextpnr
# reports for clk is the kernel's.
set -eu
cd "$(dirname "$0")/.."

K=${1:-xorshift}
TC=${TC:-/home/jayjay/dev2/lib/fpgatoolchain}
NEXTPNR=${NEXTPNR:-$TC/openxc7/bin/nextpnr-xilinx}
R=..            # the dynamatic frontend writes under the REPO ROOT build/,
                # not cells/build/ -- two different trees with the same name
HW=$R/build/dynbaseline/$K/comp/hw.mlir
OUT=$R/build/dynbaseline/$K/pnr
V=$R/build/dynbaseline/$K/verilog
SH=$R/build/dynshadow
[ -e "$HW" ] || { echo "no $HW -- run the dynamatic frontend for $K first"; exit 2; }

rm -rf "$SH"; mkdir -p "$SH/bin/generators"
ln -s "$(readlink -f $R/dynamatic/data)" "$SH/data"
for g in $R/dynamatic/build/bin/rtl-*-generator*; do
    ln -s "$(readlink -f "$g")" "$SH/bin/generators/$(basename "$g")"
done

rm -rf "$V"
$R/dynamatic/build/bin/export-rtl "$HW" "$V" $R/dynamatic/data/rtl-config-verilog.json \
    --hdl=verilog --dynamatic-path="$SH"
nvhd=$(find "$V" -name '*.vhd' | wc -l)
[ "$nvhd" -eq 0 ] || { echo "$nvhd VHDL file(s) emitted -- wrong RTL config"; exit 1; }
echo "export-rtl: $(find "$V" -name '*.v' | wc -l) Verilog files, 0 VHDL"
echo "buffers on the rings (one DV-latency slot per ring is 1 cycle/iteration):"
grep -o 'BUFFER_TYPE = "[A-Z_]*"' "$HW" | sort | uniq -c | sed 's/^/  /'

mkdir -p "$OUT"
cat > "$OUT/dyn_top.xdc" <<'XDC'
set_property PACKAGE_PIN W14 [get_ports led_red]
set_property IOSTANDARD LVCMOS33 [get_ports led_red]
set_property PACKAGE_PIN W13 [get_ports led_green]
set_property IOSTANDARD LVCMOS33 [get_ports led_green]
set_property PACKAGE_PIN U18 [get_ports clk_p]
set_property IOSTANDARD LVCMOS33 [get_ports clk_p]
XDC
# The wrapper is generated from the exported top's own port list --
# hw/dyn_wrap.py's header says why hardcoding one kernel's ports was
# wrong.
python3 hw/dyn_wrap.py "$V/$K.v" "$K" > "$OUT/dyn_top.v"

"$TC/openxc7/bin/yosys" -p "
read_verilog -lib -specify $TC/openxc7/share/yosys/xilinx/cells_sim.v
read_verilog -lib $TC/openxc7/share/yosys/xilinx/cells_xtra.v
read_verilog $(find "$V" -name '*.v' | tr '\n' ' ') $OUT/dyn_top.v
synth_xilinx -family xc7 -top dyn_top -flatten -nosrl -nolutram -nobram -noclkbuf
write_json $OUT/dyn_top.json
" > "$OUT/synth.log" 2>&1 || { echo "SYNTH FAILED"; tail -20 "$OUT/synth.log"; exit 1; }

# --freq is deliberately far above anything this reaches: nextpnr reports the
# achieved maximum either way, and without a target it "passes" at 12 MHz and
# says nothing at all.
"$NEXTPNR" --chipdb "$TC/openxc7/xc7z010clg400.bin" --xdc "$OUT/dyn_top.xdc" \
    --ignore-loops --freq 250 --timing-allow-fail \
    --json "$OUT/dyn_top.json" --write "$OUT/routed.json" --sdf "$OUT/dyn_top.sdf" \
    > "$OUT/pnr.log" 2>&1 || { echo "PNR FAILED"; tail -20 "$OUT/pnr.log"; exit 1; }

f=$(grep -oP "(?<=Max frequency for clock 'clk': )[0-9.]+" "$OUT/pnr.log" | tail -1)
echo
echo "$K through Dynamatic, routed on xc7z010clg400-1:"
python3 -c "
f=$f
print(f'  Fmax          {f:.2f} MHz')
print(f'  period        {1000.0/f:.2f} ns')
print(f'  per iteration {1000.0/f:.2f} ns  (1 cycle -- see the buffer table above)')"
