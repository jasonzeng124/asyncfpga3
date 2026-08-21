#!/usr/bin/env bash
# build_mem.sh -- build+route+bitstream for the B1/B2/B3 memory harnesses.
#
#   cells/hw/build_mem.sh mem_bist_ps                                  # B1
#   cells/hw/build_mem.sh mem_port_ps bufg1                             # B2a
#   BD_DEFINES="-DBD_MEM_USE_BUFG=0" \
#       cells/hw/build_mem.sh mem_port_ps bufg0                         # B2b
#   BD_DEFINES="-DBD_MEM_DSETUP=2 -DBD_MEM_DCO=10 -DBD_MEM_USE_BUFG=0" \
#       cells/hw/build_mem.sh mem_port_ps derived                       # B3
#
# Deliberately separate from build_hw.sh (owned by another agent) and from
# flow.sh/soak_top.v (cells/build/pnr, owned by the tighten.py gate) -- own
# sources, own output tree (build/hw_mem/<top>/<variant>/), own toolchain-log
# stamp name, so nobody else's concurrent build can clobber this one and vice
# versa. Modeled on build_hw.sh's flow (same yosys/nextpnr command shapes)
# but without its per-design SRCS table -- there are exactly two tops here
# and both just want rtl/*.v + their own hw/ file.
set -eu

cd "$(dirname "$0")/.."

TOP=${1:?"usage: build_mem.sh <mem_bist_ps|mem_port_ps> [variant]"}
VARIANT=${2:-default}

case "$TOP" in
  mem_bist_ps|mem_port_ps) ;;
  *) echo "build_mem.sh only knows mem_bist_ps and mem_port_ps"; exit 2 ;;
esac

SRCS="rtl/*.v hw/$TOP.v"

TC=${TC:-/home/jayjay/dev2/lib/fpgatoolchain}
YOSYS=$TC/openxc7/bin/yosys
NEXTPNR=$TC/openxc7/bin/nextpnr-xilinx
CHIPDB=$TC/openxc7/xc7z010clg400.bin
CELLS_SIM=$TC/openxc7/share/yosys/xilinx/cells_sim.v
CELLS_XTRA=$TC/openxc7/share/yosys/xilinx/cells_xtra.v
PART=${PART:-xc7z010clg400-1}
PRJXRAY_DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7
PRJXRAY_SRC=$TC/openxc7-src/prjxray
FASM2FRAMES=$PRJXRAY_SRC/utils/fasm2frames.py
FRAMES2BIT=$TC/openxc7/bin/xc7frames2bit

OUT=build/hw_mem/$TOP/$VARIANT
mkdir -p "$OUT"

# shellcheck disable=SC2086
for f in "$YOSYS" "$NEXTPNR" "$CHIPDB" "$CELLS_SIM" "$CELLS_XTRA" \
         "$FASM2FRAMES" "$FRAMES2BIT" $SRCS; do
    [ -e "$f" ] || { echo "missing: $f"; exit 2; }
done

echo "== toolchain =="
# Existing is not the same as correct -- prove the installed nextpnr carries
# every patch in patches/ before trusting anything it routes.  BD_STAMP names
# this exact build in cells/build/toolchain.log so a routed number can be
# attributed weeks later to the binary that actually produced it.
if ! BD_STAMP="build_mem:$TOP:$VARIANT" \
     "$(dirname "$0")/../verify/toolchain.sh" "$NEXTPNR" > "$OUT/toolchain.txt" 2>&1; then
    cat "$OUT/toolchain.txt"
    echo "toolchain.sh reported MISSING patches -- STOP, do not build on this binary"
    exit 1
fi
cat "$OUT/toolchain.txt"
SHA=$(sha256sum "$NEXTPNR" | cut -d' ' -f1)
echo "$SHA" > "$OUT/nextpnr.sha256"
echo "nextpnr sha256: $SHA"

# Same two LEDs every other hw/ design anchors the packer with.
cat > "$OUT/$TOP.xdc" <<'EOF'
set_property PACKAGE_PIN W14 [get_ports led_red]
set_property IOSTANDARD LVCMOS33 [get_ports led_red]
set_property PACKAGE_PIN W13 [get_ports led_green]
set_property IOSTANDARD LVCMOS33 [get_ports led_green]
EOF

echo "== synthesis =="
# -noclkbuf everywhere, always -- not just for USE_BUFG=0.  yosys's clkbufmap
# inserts a global buffer on anything reaching a clock pin unasked; the only
# buffer allowed on bd_mem's manufactured clock is the one bd_mem.v itself
# instantiates (BUFG or LUT1, per USE_BUFG).  -noclkbuf does not remove an
# EXPLICIT instantiation, only automatic insertion, so USE_BUFG=1 still gets
# its one real BUFG.  Same reasoning as flow.sh and build_hw.sh.
"$YOSYS" -p "
read_verilog -lib -specify $CELLS_SIM
read_verilog -lib $CELLS_XTRA
read_verilog ${BD_DEFINES:-} $SRCS
synth_xilinx -family xc7 -flatten -nodsp -nosrl -nolutram -nobram -noclkbuf -top $TOP -run begin:map_luts
opt_expr -mux_undef -noclkinv
abc -luts 2:2,3,6:5,10,20
clean
techmap -map +/xilinx/ff_map.v
techmap -map +/xilinx/lut_map.v -map +/xilinx/cells_map.v -D LUT_WIDTH=6
opt_lut_ins -tech xilinx
synth_xilinx -family xc7 -flatten -nodsp -nosrl -nolutram -nobram -noclkbuf -top $TOP -run finalize:
write_json $OUT/$TOP.json
stat
" > "$OUT/synth.log" 2>&1 || { echo "SYNTH FAILED"; tail -40 "$OUT/synth.log"; exit 1; }

last=$(grep -n "^=== $TOP ===" "$OUT/synth.log" | tail -1 | cut -d: -f1)
tail -n +"$last" "$OUT/synth.log" | grep -E "^\s+[0-9]+\s+(LUT|FD|BUFG|RAMB|IBUF|OBUF|CARRY)" || true

# Relative placement, same default and same escape hatch as build_hw.sh's
# BD_RLOC: v2 stamps RLOC_GROUP on bd_link's C node + its own latch (plus a
# consuming bd_mux's join LUTs).  Neither mem_bist_ps nor mem_port_ps
# instantiates bd_link or bd_mux -- bd_mem itself is built from bd_delay
# (plain LUT1 chains) and RAMB18E1, nothing rloc_stamp.py's instance-path
# anchors match -- so this is a deliberate no-op for these two designs, kept
# on by default anyway so the *toolchain* is the same one build_hw.sh uses
# rather than a second, divergently-flagged nextpnr invocation; BD_RLOC=none
# to compare against a pre-2026-08-21-shaped route if that is ever needed.
BD_RLOC=${BD_RLOC:-v2}
if [ "$BD_RLOC" != none ]; then
    python3 "$(dirname "$0")/rloc_stamp.py" "$OUT/$TOP.json" "$OUT/$TOP.rloc.json" \
        --variant "$BD_RLOC" --report > "$OUT/rloc.log" 2>&1 || {
            echo "RLOC STAMP FAILED"; cat "$OUT/rloc.log"; exit 1; }
    mv "$OUT/$TOP.rloc.json" "$OUT/$TOP.json"
    grep -E "group|link" "$OUT/rloc.log" | tail -3
fi

echo
echo "== place and route =="
# NEXTPNR_SEED, unset by default (nextpnr's own default seed) -- set it to
# sweep placements when checking whether a derived margin is a property of
# the design or of one lucky route (see verify/tighten.py's own warning that
# every number it prints "expires the next time anything moves", and this
# project's rule-E history: the same design at four placer seeds gave 0, 6,
# 5 and 3 violations).
SEEDOPT=""
[ -n "${NEXTPNR_SEED:-}" ] && SEEDOPT="--seed ${NEXTPNR_SEED}"
# shellcheck disable=SC2086
"$NEXTPNR" --chipdb "$CHIPDB" --xdc "$OUT/$TOP.xdc" --ignore-loops $SEEDOPT \
           --json "$OUT/$TOP.json" --write "$OUT/${TOP}_routed.json" \
           --sdf "$OUT/$TOP.sdf" --fasm "$OUT/$TOP.fasm" \
           > "$OUT/pnr.log" 2>&1 \
    || { echo "PNR FAILED"; tail -40 "$OUT/pnr.log"; exit 1; }
echo "routed.${NEXTPNR_SEED:+ (seed $NEXTPNR_SEED)}"

lut_sites=$(grep -c "LUT\.INIT" "$OUT/$TOP.fasm" || true)
bufgs=$(grep -c "BUFGCTRL" "$OUT/$TOP.fasm" || true)
brams=$(grep -c "RAMB18" "$OUT/$TOP.fasm" || true)
echo "FASM: $lut_sites occupied LUT sites, $bufgs global buffer lines, $brams BRAM lines"
echo "(expect 1 BUFG for aclk-only builds e.g. mem_bist_ps; expect 2 for" \
     "mem_port_ps with USE_BUFG=1 -- aclk plus bd_mem's manufactured clock;" \
     "expect 1 for mem_port_ps with USE_BUFG=0 -- ram_clk must NOT show" \
     "here, it is a LUT1 not a BUFGCTRL)"

echo
echo "== bitstream =="
PYTHONPATH="$PRJXRAY_SRC:$TC/openxc7/lib/python${PYTHONPATH:+:$PYTHONPATH}" \
    python3 "$FASM2FRAMES" --db-root "$PRJXRAY_DB" --part "$PART" \
    "$OUT/$TOP.fasm" > "$OUT/$TOP.frames" 2> "$OUT/frames.log" \
    || { echo "FASM2FRAMES FAILED"; tail -20 "$OUT/frames.log"; exit 1; }

"$FRAMES2BIT" --part_file "$PRJXRAY_DB/$PART/part.yaml" --part_name "$PART" \
    --frm_file "$OUT/$TOP.frames" --output_file "$OUT/$TOP.bit" \
    > "$OUT/bit.log" 2>&1 \
    || { echo "FRAMES2BIT FAILED"; tail -20 "$OUT/bit.log"; exit 1; }

[ -s "$OUT/$TOP.bit" ] || { echo "empty bitstream"; exit 1; }
echo "$(stat -c%s "$OUT/$TOP.bit") bytes -> $OUT/$TOP.bit"
echo "routed SDF -> $OUT/$TOP.sdf"
echo "nextpnr sha256 (BUILD time) -> $SHA"
echo
echo "build_mem.sh PASS: $OUT/$TOP.bit"
