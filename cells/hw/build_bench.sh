#!/usr/bin/env bash
# Build a generalised per-kernel benchmark bitstream (see hw/gen_bench.py):
#
#   hw/build_bench.sh gcd            # real bdc_gcd DUT, module gcd_bench
#   hw/build_bench.sh gcd --null     # trivial pass-through control, same shape
#
# This is a SIBLING of build_hw.sh, not a patch to it -- build_hw.sh is owned
# by someone else's concurrent work on the mult* designs and is explicitly
# off limits here.  It duplicates build_hw.sh's synth/PnR/bitstream recipe
# (same toolchain paths, same flags, same DSP note) because that recipe is
# correct and there is no reason to diverge from it; what's NEW is generating
# the bench top itself from the kernel's own signature (hw/gen_bench.py)
# instead of hand-writing one file per kernel the way hw/gcd_bench.v was.
#
# Every kernel in kernels/ needs the SAME two build steps before synthesis:
#   1. bdc/emit.py --no-top on build/frontend/<kernel>/comp/handshake_transformed.mlir
#      -> build/gen/<kernel>_kernel_bench.v (module bdc_<kernel>), exactly
#      the way build_hw.sh's gcd_ps/gcd_bench cases do it.
#   2. hw/gen_bench.py <kernel> [--null] -> build/gen/<kernel>[_null]_bench.v
#      (the bridge+FSM+PS7 top), driven entirely by the parsed function
#      signature -- see gen_bench.py's header for why.
set -eu

cd "$(dirname "$0")/.."

KERNEL=${1:-}
NULL=0
if [ "${2:-}" = "--null" ]; then NULL=1; fi

case "$KERNEL" in
    gcd|ipow|collatz|collatz64|isprime|xorshift) ;;
    *) echo "usage: hw/build_bench.sh <gcd|ipow|collatz|collatz64|isprime|xorshift> [--null]"
       exit 2 ;;
esac

# Every OTHER path in this script (SRCS, $OUT, the synth/PnR/bitstream
# steps below) is cells-relative, because this script's own cwd is cells/
# (see the `cd` above) and stays there the whole run -- no subshell `cd ..`
# anywhere, unlike an earlier draft of this file, which cd'd into the repo
# root just for the emit.py call and wrote build/gen/*_kernel_bench.v
# there instead of into cells/build/gen/ -- the SAME directory this
# script's own SRCS/synthesis step reads from moments later. That silently
# produced "missing: build/gen/gcd_kernel_bench.v" because the file really
# was missing, just one directory over. bdc/emit.py itself still lives at
# the repo root (one level above cells/), so it is invoked via "../bdc/emit.py"
# from here instead, and the .mlir path handed to it is likewise
# "../build/frontend/...", keeping every read AND every write on the
# cells-relative side of the fence.
MLIR="../build/frontend/$KERNEL/comp/handshake_transformed.mlir"
[ -e "$MLIR" ] || { echo "missing: $MLIR (kernel not compiled to handshake IR yet)"; exit 2; }

mkdir -p build/gen
python3 ../bdc/emit.py "$MLIR" --no-top -o "build/gen/${KERNEL}_kernel_bench.v"

# TOP is deliberately "_bench_gen"/"_null_bench_gen", NOT "_bench": build_hw.sh
# (owned by someone else, off limits) already has a "gcd_bench" case that
# builds the OLD hand-written hw/gcd_bench.v to output directory
# build/hw/gcd_bench/. This generator's default top name from gen_bench.py
# is "<kernel>_bench" -- identical to that -- so building it under that name
# would land in the SAME build/hw/gcd_bench/ directory and silently
# overwrite the other harness's bitstream (confirmed on disk: a gcd_bench.bit
# already exists there, built via build_hw.sh, and is presumably still live
# on the board or referenced by someone else's run). --top here renames both
# the generated Verilog module AND, through TOP below, this script's own
# output directory, so the two builds can never collide.
if [ "$NULL" = "1" ]; then
    TOP="${KERNEL}_null_bench_gen"
    python3 hw/gen_bench.py "$KERNEL" --null --top "$TOP" -o "build/gen/${TOP}.v"
else
    TOP="${KERNEL}_bench_gen"
    python3 hw/gen_bench.py "$KERNEL" --top "$TOP" -o "build/gen/${TOP}.v"
fi

SRCS="rtl/*.v build/gen/${KERNEL}_kernel_bench.v build/gen/${TOP}.v"

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

OUT=build/hw/$TOP
mkdir -p "$OUT"

# shellcheck disable=SC2086
for f in "$YOSYS" "$NEXTPNR" "$CHIPDB" "$CELLS_SIM" "$CELLS_XTRA" \
         "$FASM2FRAMES" "$FRAMES2BIT" $SRCS; do
    [ -e "$f" ] || { echo "missing: $f"; exit 2; }
done

# Same gate build_hw.sh runs before its own nextpnr call: proves the
# installed binary carries every patch this project's routed numbers rely
# on, not just that a binary exists at the path. Appends provenance
# (timestamp, sha256, verdict) to build/toolchain.log. MISSING here means
# STOP, per the harness spec -- do not work around it.
"$(dirname "$0")/../verify/toolchain.sh" "$NEXTPNR"

cat > "$OUT/$TOP.xdc" <<EOF
set_property PACKAGE_PIN W14 [get_ports led_red]
set_property IOSTANDARD LVCMOS33 [get_ports led_red]
set_property PACKAGE_PIN W13 [get_ports led_green]
set_property IOSTANDARD LVCMOS33 [get_ports led_green]
EOF

echo "== synthesis ($TOP) =="
# BD_DSP note: see build_hw.sh and cells/flow.sh -- default OFF (-nodsp),
# BD_DSP=1 re-enables DSP48E1 inference for anyone tracking the fix on the
# other branch.  Whichever setting a bitstream was built with, the host
# report stamps it, per the harness spec's "stamp results with the BD_DSP
# setting used" requirement.
DSPOPT="-nodsp"
[ "${BD_DSP:-0}" = "1" ] && DSPOPT=""

"$YOSYS" -p "
read_verilog -lib -specify $CELLS_SIM
read_verilog -lib $CELLS_XTRA
read_verilog ${BD_DEFINES:-} $SRCS
synth_xilinx -family xc7 -flatten $DSPOPT -nosrl -nolutram -nobram -noclkbuf -top $TOP -run begin:map_luts
opt_expr -mux_undef -noclkinv
abc -luts 2:2,3,6:5,10,20
clean
techmap -map +/xilinx/ff_map.v
techmap -map +/xilinx/lut_map.v -map +/xilinx/cells_map.v -D LUT_WIDTH=6
opt_lut_ins -tech xilinx
synth_xilinx -family xc7 -flatten $DSPOPT -nosrl -nolutram -nobram -noclkbuf -top $TOP -run finalize:
write_json $OUT/$TOP.json
stat
" > "$OUT/synth.log" 2>&1 || { echo "SYNTH FAILED"; tail -40 "$OUT/synth.log"; exit 1; }

last=$(grep -n "^=== $TOP ===" "$OUT/synth.log" | tail -1 | cut -d: -f1)
tail -n +"$last" "$OUT/synth.log" | grep -E "^\s+[0-9]+\s+(LUT|FD|BUFG|BSCAN|IBUF|OBUF|CARRY)" || true

echo
echo "== place and route =="
SEED=""
[ -n "${NEXTPNR_SEED:-}" ] && SEED="--seed ${NEXTPNR_SEED}"

# shellcheck disable=SC2086
"$NEXTPNR" --chipdb "$CHIPDB" --xdc "$OUT/$TOP.xdc" --ignore-loops $SEED \
           --json "$OUT/$TOP.json" --write "$OUT/${TOP}_routed.json" \
           --sdf "$OUT/$TOP.sdf" --fasm "$OUT/$TOP.fasm" \
           > "$OUT/pnr.log" 2>&1 \
    || { echo "PNR FAILED"; tail -40 "$OUT/pnr.log"; exit 1; }
echo "routed."

lut_sites=$(grep -c "LUT\.INIT" "$OUT/$TOP.fasm" || true)
bufgs=$(grep -c "BUFGCTRL" "$OUT/$TOP.fasm" || true)
echo "FASM:  $lut_sites occupied LUT sites, $bufgs global buffer lines"

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
echo "BD_DSP=${BD_DSP:-0}"
echo
echo "build_bench.sh PASS"
