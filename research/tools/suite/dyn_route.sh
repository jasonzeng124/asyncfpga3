#!/usr/bin/env bash
# dyn_route.sh KERNEL VDIR OUTDIR SEED... -- Dynamatic's exported Verilog (research/tools/suite/dyn_export.py) routed
# on our part with our toolchain, one route per placer seed; prints one line per seed and a summary line.
# The method of cells/hw/dyn_baseline.sh (2026-08, the three "measured" figures): the kernel inside cells/hw/dyn_wrap.py's
# I/O-bound wrapper (inputs off registers, outputs XOR-reduced into registers, so the clk period is the kernel's own),
# yosys synth_xilinx -flatten -nosrl -nolutram -nobram -noclkbuf, nextpnr-xilinx --ignore-loops --timing-allow-fail
# with --freq 250 (far above what it reaches: nextpnr reports the achieved maximum either way, and without a target it
# "passes" at 12 MHz); the period is 1000 / nextpnr's "Max frequency for clock 'clk'". Differences from 2026-08: an
# explicit --seed per route (dyn_baseline.sh passed none: one route at the default seed), and the export is ours.
# Run cells/verify/toolchain.sh first; the nextpnr sha256 is printed in the summary line.
set -uo pipefail
K=$1; V=$(cd "$2" && pwd); O=$3; shift 3
R=$(cd "$(dirname "$0")/../../.." && pwd)
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
NEXTPNR=${NEXTPNR:-$TC/openxc7/bin/nextpnr-xilinx}
mkdir -p "$O"; O=$(cd "$O" && pwd)
cat > "$O/dyn_top.xdc" <<'XDC'
set_property PACKAGE_PIN W14 [get_ports led_red]
set_property IOSTANDARD LVCMOS33 [get_ports led_red]
set_property PACKAGE_PIN W13 [get_ports led_green]
set_property IOSTANDARD LVCMOS33 [get_ports led_green]
set_property PACKAGE_PIN U18 [get_ports clk_p]
set_property IOSTANDARD LVCMOS33 [get_ports clk_p]
XDC
python3 "$R/cells/hw/dyn_wrap.py" "$V/$K.v" "$K" > "$O/dyn_top.v" || { echo "$K WRAP FAILED"; exit 1; }
if [ ! -s "$O/dyn_top.json" ]; then
  "$TC/openxc7/bin/yosys" -p "
read_verilog -lib -specify $TC/openxc7/share/yosys/xilinx/cells_sim.v
read_verilog -lib $TC/openxc7/share/yosys/xilinx/cells_xtra.v
read_verilog $(find "$V" -name '*.v' | sort | tr '\n' ' ') $O/dyn_top.v
synth_xilinx -family xc7 -top dyn_top -flatten -nosrl -nolutram -nobram -noclkbuf
write_json $O/dyn_top.json
" > "$O/synth.log" 2>&1 || { echo "$K SYNTH FAILED ($(tail -1 "$O/synth.log"))"; exit 1; }
fi
luts=$(grep -E "^\s+[0-9]+\s+LUT[1-6]$" "$O/synth.log" | tail -6 | awk "{s += \$1} END {print s + 0}")
ps=""
for S in "$@"; do
  "$NEXTPNR" --chipdb "$TC/openxc7/xc7z010clg400.bin" --xdc "$O/dyn_top.xdc" --ignore-loops --seed "$S" \
      --freq 250 --timing-allow-fail --json "$O/dyn_top.json" --write "$O/routed_$S.json" > "$O/pnr_$S.log" 2>&1 \
    || { echo "$K seed $S PNR FAILED ($(tail -1 "$O/pnr_$S.log"))"; continue; }
  f=$(grep -oP "(?<=Max frequency for clock 'clk': )[0-9.]+" "$O/pnr_$S.log" | tail -1)
  [ -n "$f" ] || { echo "$K seed $S: no Fmax line"; continue; }
  p=$(python3 -c "print('%.3f' % (1000.0 / $f))")
  echo "$K seed $S Fmax $f MHz period $p ns"
  ps="$ps $p"
  rm -f "$O/routed_$S.json"
done
sha=$(sha256sum "$NEXTPNR" | cut -c1-16)
python3 - "$K" "$luts" "$sha" $ps <<'PY'
import statistics, sys
k, luts, sha = sys.argv[1:4]
p = [float(x) for x in sys.argv[4:]]
if p:
    print("%s period %d routes: mean %.3f ns, range %.3f-%.3f; synth LUTs %s; nextpnr %s" % (
        k, len(p), statistics.mean(p), min(p), max(p), luts, sha))
else:
    print("%s: no route" % k)
PY
