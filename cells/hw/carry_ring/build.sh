#!/usr/bin/env bash
# Build carry_ro_top to a bitstream: hw/build_hw.sh's recipe (BD_NO_TIGHTEN=1
# BD_RLOC=none path, the one ro_many_top was built with), for a source outside
# cells/hw/.  Same yosys script, same nextpnr flags plus a seed and --freq,
# same fasm_audit, same fasm2frames / xc7frames2bit.
#
#   cells/hw/carry_ring/build.sh OUTDIR SEED [FREQ_MHZ]
#
# Writes OUTDIR/carry_ro_top.{json,_routed.json,sdf,fasm,frames,bit},
# toolchain.txt, synth.log, pnr.log.  Exits nonzero on any failure, including
# toolchain.sh (CLAUDE.md: nothing routed by a failing toolchain is a result).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
CELLS=$(cd "$HERE/../.." && pwd)
OUT=${1:?OUTDIR}
SEED=${2:?SEED}
FREQ=${3:-100}
TOP=carry_ro_top
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)

TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
YOSYS=$TC/openxc7/bin/yosys
NEXTPNR=${NEXTPNR:-$TC/openxc7/bin/nextpnr-xilinx}
CHIPDB=$TC/openxc7/xc7z010clg400.bin
CELLS_SIM=$TC/openxc7/share/yosys/xilinx/cells_sim.v
CELLS_XTRA=$TC/openxc7/share/yosys/xilinx/cells_xtra.v
PART=${PART:-xc7z010clg400-1}
PRJXRAY_DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7
PRJXRAY_SRC=$TC/openxc7-src/prjxray
FASM2FRAMES=$PRJXRAY_SRC/utils/fasm2frames.py
FRAMES2BIT=$TC/openxc7/bin/xc7frames2bit

"$CELLS/verify/toolchain.sh" "$NEXTPNR"
{
    printf 'nextpnr %s  %s\n' "$(sha256sum "$NEXTPNR" | cut -c1-16)" "$NEXTPNR"
    printf 'seed %s  freq %s MHz  source md5 %s\n' "$SEED" "$FREQ" "$(md5sum < "$HERE/$TOP.v" | cut -c1-32)"
    "$CELLS/verify/toolchain.sh" "$NEXTPNR" 2>&1
} > "$OUT/toolchain.txt"

cat > "$OUT/$TOP.xdc" <<'EOF'
set_property PACKAGE_PIN W14 [get_ports led_red]
set_property IOSTANDARD LVCMOS33 [get_ports led_red]
set_property PACKAGE_PIN W13 [get_ports led_green]
set_property IOSTANDARD LVCMOS33 [get_ports led_green]
EOF

echo "== synthesis =="
"$YOSYS" -p "
read_verilog -lib -specify $CELLS_SIM
read_verilog -lib $CELLS_XTRA
read_verilog $HERE/$TOP.v
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
" > "$OUT/synth.log" 2>&1 || { echo "SYNTH FAILED"; tail -40 "$OUT/synth.log"; exit 1; }
last=$(grep -n "^=== $TOP ===" "$OUT/synth.log" | tail -1 | cut -d: -f1)
tail -n +"$last" "$OUT/synth.log" | grep -E "^\s+[0-9]+\s+(LUT|FD|BUFG|BSCAN|CARRY|MUXF)" || true

echo "== place and route (seed $SEED, --freq $FREQ) =="
"$NEXTPNR" --chipdb "$CHIPDB" --xdc "$OUT/$TOP.xdc" --ignore-loops --seed "$SEED" \
           --freq "$FREQ" --timing-allow-fail \
           --json "$OUT/$TOP.json" --write "$OUT/${TOP}_routed.json" \
           --sdf "$OUT/$TOP.sdf" --fasm "$OUT/$TOP.fasm" \
           > "$OUT/pnr.log" 2>&1 \
    || { echo "PNR FAILED"; tail -40 "$OUT/pnr.log"; exit 1; }
echo "routed."
echo "FASM:  $(grep -c 'LUT\.INIT' "$OUT/$TOP.fasm" || true) LUT sites, $(grep -c 'BUFGCTRL' "$OUT/$TOP.fasm" || true) BUFGCTRL lines, $(grep -c 'CARRY4' "$OUT/$TOP.fasm" || true) CARRY4 lines"
( cd "$CELLS" && python3 verify/fasm_audit.py "$OUT/${TOP}_routed.json" "$OUT/$TOP.fasm" --synth "$OUT/$TOP.json" ) \
    || { echo "FASM AUDIT FAILED -- the bitstream would not be the netlist"; exit 1; }

echo "== bitstream =="
PYTHONPATH="$PRJXRAY_SRC:$TC/openxc7/lib/python${PYTHONPATH:+:$PYTHONPATH}" \
    python3 "$FASM2FRAMES" --db-root "$PRJXRAY_DB" --part "$PART" \
    "$OUT/$TOP.fasm" > "$OUT/$TOP.frames" 2> "$OUT/frames.log" \
    || { echo "FASM2FRAMES FAILED"; tail -20 "$OUT/frames.log"; exit 1; }
"$FRAMES2BIT" --part_file "$PRJXRAY_DB/$PART/part.yaml" --part_name "$PART" \
    --frm_file "$OUT/$TOP.frames" --output_file "$OUT/$TOP.bit" \
    > "$OUT/bit.log" 2>&1 || { echo "FRAMES2BIT FAILED"; tail -20 "$OUT/bit.log"; exit 1; }
[ -s "$OUT/$TOP.bit" ] || { echo "empty bitstream"; exit 1; }
echo "$(md5sum < "$OUT/$TOP.bit" | cut -c1-32)  $OUT/$TOP.bit"
echo "build.sh PASS"
