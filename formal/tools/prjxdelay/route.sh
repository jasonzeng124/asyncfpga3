#!/usr/bin/env bash
# Re-route a ring design exactly as cells/hw/build_hw.sh routes it (same yosys
# script, same nextpnr options), into formal/tools/prjxdelay/build/ instead of
# cells/build/ (cells/ is read-only for this probe).  No bitstream: the delay
# model reads the FASM, the routed JSON and the SDF.
#
#     formal/tools/prjxdelay/route.sh TOP SEED [FREQ]
#
# TOP  = ro_many_top | ro_top.   SEED = "default" (no --seed: what build_hw.sh
# does when NEXTPNR_SEED is unset, i.e. how the measured bitstreams were built)
# or an integer.  FREQ: optional --freq (build_hw.sh passes none unless
# NEXTPNR_FREQ is set; the measured ro builds did not set it).
# BD_RLOC=none: the 128-ring measurement was built that way (ro_many_measure.py
# docstring), and ro_top's 2026-08-18 rebuild predates RLOC (2026-08-21).
set -euo pipefail
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
TOP=$1; SEED=$2; FREQ=${3:-}
TAG=${TOP}_s${SEED}${FREQ:+_f$FREQ}
OUT=$HERE/build/$TAG; mkdir -p "$OUT"
cd "$REPO/cells"
BD_TOOLCHAIN_LOG=$OUT/toolchain.log verify/toolchain.sh > "$OUT/toolchain.txt" 2>&1 \
    || { cat "$OUT/toolchain.txt"; echo "toolchain.sh FAILED"; exit 1; }
printf 'nextpnr %s\n' "$(sha256sum "$TC/openxc7/bin/nextpnr-xilinx" | cut -c1-16)" >> "$OUT/toolchain.txt"
SRCS="rtl/bd_latch.v rtl/bd_ce.v rtl/bd_arb.v hw/$TOP.v"
cat > "$OUT/$TOP.xdc" <<'EOF'
set_property PACKAGE_PIN W14 [get_ports led_red]
set_property IOSTANDARD LVCMOS33 [get_ports led_red]
set_property PACKAGE_PIN W13 [get_ports led_green]
set_property IOSTANDARD LVCMOS33 [get_ports led_green]
EOF
"$TC/openxc7/bin/yosys" -p "
read_verilog -lib -specify $TC/openxc7/share/yosys/xilinx/cells_sim.v
read_verilog -lib $TC/openxc7/share/yosys/xilinx/cells_xtra.v
read_verilog $SRCS
synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -top $TOP -run begin:map_luts
opt_expr -mux_undef -noclkinv
abc -luts 2:2,3,6:5,10,20
clean
techmap -map +/xilinx/ff_map.v
techmap -map +/xilinx/lut_map.v -map +/xilinx/cells_map.v -D LUT_WIDTH=6
opt_lut_ins -tech xilinx
synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -top $TOP -run finalize:
write_json $OUT/$TOP.json
stat
" > "$OUT/synth.log" 2>&1 || { tail -30 "$OUT/synth.log"; exit 1; }
SEEDOPT=""; [ "$SEED" != default ] && SEEDOPT="--seed $SEED"
FREQOPT=""; [ -n "$FREQ" ] && FREQOPT="--freq $FREQ --timing-allow-fail"
# shellcheck disable=SC2086
"$TC/openxc7/bin/nextpnr-xilinx" --chipdb "$TC/openxc7/xc7z010clg400.bin" --xdc "$OUT/$TOP.xdc" \
    --ignore-loops $SEEDOPT $FREQOPT --json "$OUT/$TOP.json" --write "$OUT/${TOP}_routed.json" \
    --sdf "$OUT/$TOP.sdf" --fasm "$OUT/$TOP.fasm" > "$OUT/pnr.log" 2>&1 \
    || { tail -30 "$OUT/pnr.log"; echo "PNR FAILED"; exit 1; }
python3 verify/fasm_audit.py "$OUT/${TOP}_routed.json" "$OUT/$TOP.fasm" --synth "$OUT/$TOP.json" \
    > "$OUT/fasm_audit.log" 2>&1 || { tail "$OUT/fasm_audit.log"; echo "FASM AUDIT FAILED"; exit 1; }
echo "routed $TAG  fasm sha $(sha256sum "$OUT/$TOP.fasm" | cut -c1-16)"
