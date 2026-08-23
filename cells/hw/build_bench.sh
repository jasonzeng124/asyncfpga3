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
# output directory, so the two builds can never collide.  Computed up front
# (rather than down where gen_bench.py is invoked) because the default-
# tighten dispatch just below needs it before anything else in this script
# runs.
if [ "$NULL" = "1" ]; then
    TOP="${KERNEL}_null_bench_gen"
else
    TOP="${KERNEL}_bench_gen"
fi

# Default build path: tighten, same treatment as hw/build_hw.sh (see its
# header) -- but that script is off limits to patch, and converge.sh
# hardcoded "./hw/build_hw.sh $DESIGN" as the builder it iterates, one
# positional token, while this script takes "<kernel> [--null]".
# CONVERGE_BUILDER (verify/converge.sh) is the parameterisation that lets
# ONE loop drive both shapes without duplicating it here: point it at this
# script plus this invocation's own args, and DESIGN becomes $TOP so
# converge.sh's build/hw/$DESIGN/$DESIGN.sdf bookkeeping lines up with the
# --top name below.
#
# BDC_SELECT_PADS already being set is the re-entry signal (converge.sh
# always sets it, first iteration included) -- just build.  BD_NO_TIGHTEN=1
# skips convergence and builds with bdc/emit.py's unmeasured SELECT_PAD=4
# estimate, unchanged from before this existed.
#
# The --null DUT has no bd_link/bd_pipe at all (see the BD_RLOC note further
# down), hence no bd_steer/bd_mux either -- rule E finds zero select gates on
# it, same as ro_top/arb_mtbf/arb_prot, and converge.sh already treats a
# zero-deficit first measurement as CONVERGED, so this costs exactly the one
# build it would have cost anyway.
if [ -z "${BDC_SELECT_PADS:-}" ] && [ "${BD_NO_TIGHTEN:-0}" != "1" ]; then
    BUILDER_ARGS=("$KERNEL")
    [ "$NULL" = "1" ] && BUILDER_ARGS+=(--null)
    echo "build_bench.sh: MODE=converge -- no BDC_SELECT_PADS (not a" \
         "re-entry) and no BD_NO_TIGHTEN; handing off to verify/converge.sh" \
         "for $TOP" >&2
    exec env CONVERGE_BUILDER="./hw/build_bench.sh ${BUILDER_ARGS[*]}" \
        "$(dirname "$0")/../verify/converge.sh" "$TOP"
fi
if [ "${BD_NO_TIGHTEN:-0}" = "1" ]; then
    echo "build_bench.sh: MODE=BD_NO_TIGHTEN -- building $TOP directly," \
         "select channels at bdc/emit.py's unmeasured SELECT_PAD estimate" >&2
else
    echo "build_bench.sh: MODE=converge re-entry" \
         "(BDC_SELECT_PADS=$BDC_SELECT_PADS) -- building $TOP" >&2
fi

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

# TOP itself was computed above, before the default-tighten dispatch; this is
# just the gen_bench.py call the dispatch had no reason to duplicate.
if [ "$NULL" = "1" ]; then
    python3 hw/gen_bench.py "$KERNEL" --null --top "$TOP" -o "build/gen/${TOP}.v"
else
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

# Drop the previous bitstream BEFORE doing anything else.  Every failure path
# below exits without touching $TOP.bit, so a build that dies in synthesis, in
# placement, or on the timing gate used to leave the PREVIOUS run's bitstream
# sitting there -- and run_all_bench.sh checks only that the file exists, so it
# would program and measure it, reporting last week's design under this week's
# name.  Caught when gcd_null failed the 100 MHz gate and the sweep queued up
# behind it was about to measure a bitstream built 83 minutes earlier.  Absent
# is a result you can act on; stale is one you cannot detect.
rm -f "$OUT/$TOP.bit"

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
# BD_DSP note: the DSP48E1 constant-pins bug (A operand gated to zero by an
# unwired INMODE tile default) is FIXED -- patches/nextpnr-xilinx-dsp-constpins.patch,
# gated by verify/toolchain.sh, so a binary without the patch cannot silently
# build this.  flow.sh and build_hw.sh both default BD_DSP=1 now; this script
# matches them.  BD_DSP=0 remains an escape hatch for bisecting a future
# toolchain change, not a safety default -- leaving it off costs LUT
# multipliers (and, per compute.py's 2*width matched-delay pricing, ~9ns of
# latency it does not need) on every kernel with a variable-by-variable
# multiply, ipow first.  Whichever setting a bitstream was built with, the
# host report stamps it, per the harness spec's "stamp results with the
# BD_DSP setting used" requirement.
DSPOPT="-nodsp"
[ "${BD_DSP:-1}" = "1" ] && DSPOPT=""

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

# Relative placement.  BD_RLOC=v2 (default, matching build_hw.sh) stamps an
# RLOC_GROUP attribute on the post-synthesis netlist so nextpnr keeps each
# bd_link's C node in the same SLICE as its own latch -- see
# hw/rloc_stamp.py and patches/README.md.  The cluster floats; nothing is
# pinned.  BD_RLOC=none turns it off, and that is the ONLY way to reproduce
# a pre-2026-08-21 route: routed placement is stable per binary but not
# across binaries, so numbers from the two are not comparable.  An
# unpatched nextpnr ignores the attribute silently, which is what
# verify/toolchain.sh above is for.
#
# The null DUT (see gen_bench.py's is_null branch) is built ONLY from
# bd_join and bd_delay -- it never instantiates bd_link or bd_pipe, so it
# structurally has zero '*.ctl.u.u' / cpair controller cells for
# rloc_stamp.py to find.  That is not the "every storage cell floats" bug
# the 0-candidate check exists to catch (confirmed on disk 2026-08-21: all
# 6 null builds hit "RLOC STAMP FAILED / 0 controller(s) matched" -- the
# real per-kernel builds, which DO instantiate bd_link, all found >0 and
# passed).  Forcing BD_RLOC=none for --null is not a pinned BEL and not a
# delay pad: it is skipping a placement pass that has nothing in this
# netlist to act on.
if [ "$NULL" = "1" ]; then
    # Say it rather than doing it silently: a batch that exports BD_RLOC=v2
    # for every kernel should be able to see why the null build did not
    # cluster, instead of wondering whether the setting took.
    [ "${BD_RLOC:-}" = none ] || \
        echo "build_bench: --null has no bd_link/bd_pipe to cluster; forcing BD_RLOC=none" >&2
    BD_RLOC=none
else
    BD_RLOC=${BD_RLOC:-v2}
fi
if [ "$BD_RLOC" != none ]; then
    python3 "$(dirname "$0")/rloc_stamp.py" "$OUT/$TOP.json" "$OUT/$TOP.rloc.json" \
        --variant "$BD_RLOC" --report > "$OUT/rloc.log" 2>&1 || {
            echo "RLOC STAMP FAILED"; cat "$OUT/rloc.log"; exit 1; }
    mv "$OUT/$TOP.rloc.json" "$OUT/$TOP.json"
    grep -E "group|link" "$OUT/rloc.log" | tail -3
fi

last=$(grep -n "^=== $TOP ===" "$OUT/synth.log" | tail -1 | cut -d: -f1)
tail -n +"$last" "$OUT/synth.log" | grep -E "^\s+[0-9]+\s+(LUT|FD|BUFG|BSCAN|IBUF|OBUF|CARRY)" || true

echo
echo "== place and route =="
SEED=""
[ -n "${NEXTPNR_SEED:-}" ] && SEED="--seed ${NEXTPNR_SEED}"

# shellcheck disable=SC2086
# --freq is what makes the timing verdict MEAN anything.  Without it nextpnr
# compares against its own 12 MHz default and prints "PASS at 12.00 MHz" for a
# design the board then clocks at 100 -- which is exactly how the bridge shipped
# for twelve builds closing at 28-35 MHz while FCLK0 ran it at 100 MHz, silently
# corrupting the latency histogram (see gen_bench.py's histogram pipeline note).
# Default it to the FCLK0 this harness actually runs at.
TARGET_MHZ=${TARGET_MHZ:-100}

# One route is a sample, and a wide one: the same netlist has come back 95.19
# and 105.88 MHz on neighbouring builds.  So a miss is not automatically a
# design that cannot make the target -- it may be the seed.  Re-route on a
# fresh seed before believing a near miss, and keep the best result rather
# than whatever the last attempt happened to give.  An explicit NEXTPNR_SEED
# disables this: that is someone reproducing one specific route.
PNR_TRIES=${PNR_TRIES:-6}
[ -n "${NEXTPNR_SEED:-}" ] && PNR_TRIES=1

BEST=""
ACHIEVED=""     # stays empty if the first attempt never got as far as a number
attempt=0
while [ "$attempt" -lt "$PNR_TRIES" ]; do
    attempt=$((attempt + 1))
    TRYSEED="$SEED"
    [ -z "${NEXTPNR_SEED:-}" ] && [ "$attempt" -gt 1 ] && TRYSEED="--seed $attempt"

    # Bound each ATTEMPT, not just the build.  Asking for a frequency the router
    # cannot reach makes it iterate rather than give up: xorshift_null ran 1800
    # seconds on one seed and produced nothing, where every other null finished
    # in 35-60.  A seed that has not converged in PNR_TIMEOUT is not close, so
    # spend the time on the next seed instead of on this one.
    # shellcheck disable=SC2086
    if ! timeout "${PNR_TIMEOUT:-420}" "$NEXTPNR" --chipdb "$CHIPDB" --xdc "$OUT/$TOP.xdc" --ignore-loops $TRYSEED \
               --freq "$TARGET_MHZ" --timing-allow-fail \
               --json "$OUT/$TOP.json" --write "$OUT/${TOP}_routed.json" \
               --sdf "$OUT/$TOP.sdf" --fasm "$OUT/$TOP.fasm" \
               > "$OUT/pnr.log" 2>&1; then
        # nextpnr itself failing is ALSO seed-dependent, not just slow timing.
        # collatz64_null died on "post-placement validity check failed for Bel
        # SLICE_X8Y79/A5FF (no cell)" -- a placer bug that another seed walks
        # straight past.  Treat it as a failed attempt, not as a verdict on the
        # design, and only give up once every seed has had a turn.
        echo "PNR FAILED on attempt $attempt/$PNR_TRIES:"
        grep -E "^ERROR" "$OUT/pnr.log" | head -3 || true
        grep -qE "^ERROR" "$OUT/pnr.log" || echo "  (no ERROR line -- attempt hit the ${PNR_TIMEOUT:-420}s per-seed timeout)"
        if [ "$attempt" -lt "$PNR_TRIES" ]; then continue; fi
        echo "PNR FAILED on all $PNR_TRIES seeds -- this is not seed noise." >&2
        tail -40 "$OUT/pnr.log" >&2
        exit 1
    fi

    ACHIEVED=$(grep -oP "(?<=Max frequency for clock 'fclk0_bufg': )[0-9.]+" "$OUT/pnr.log" | tail -1)
    if [ -z "$ACHIEVED" ]; then
        echo "TIMING: no Fmax for fclk0_bufg in $OUT/pnr.log -- cannot certify this build" >&2
        exit 1
    fi
    echo "routed. (attempt $attempt/$PNR_TRIES: ${ACHIEVED} MHz)"

    # Met the target: stop here, and keep THIS route's outputs.
    if awk "BEGIN{exit !($ACHIEVED >= $TARGET_MHZ)}"; then BEST="$ACHIEVED"; break; fi

    # Missed.  Keep the best route seen so far, so a later worse seed cannot
    # overwrite a better one -- these files are the build's actual output.
    if [ -z "$BEST" ] || awk "BEGIN{exit !($ACHIEVED > $BEST)}"; then
        BEST="$ACHIEVED"
        for e in fasm sdf; do cp -f "$OUT/$TOP.$e" "$OUT/$TOP.$e.best" 2>/dev/null || true; done
        cp -f "$OUT/${TOP}_routed.json" "$OUT/${TOP}_routed.json.best" 2>/dev/null || true
        cp -f "$OUT/pnr.log" "$OUT/pnr.log.best" 2>/dev/null || true
    fi
done

# If no attempt met the target, restore the best one we saw.
if [ -n "$ACHIEVED" ] && awk "BEGIN{exit !($ACHIEVED < $TARGET_MHZ)}" && [ -e "$OUT/$TOP.fasm.best" ]; then
    for e in fasm sdf; do mv -f "$OUT/$TOP.$e.best" "$OUT/$TOP.$e"; done
    mv -f "$OUT/${TOP}_routed.json.best" "$OUT/${TOP}_routed.json"
    mv -f "$OUT/pnr.log.best" "$OUT/pnr.log"
    ACHIEVED="$BEST"
    echo "keeping the best of $PNR_TRIES routes: ${ACHIEVED} MHz"
fi
rm -f "$OUT/$TOP".*.best "$OUT/${TOP}_routed.json.best" "$OUT/pnr.log.best"
echo "TIMING: fclk0_bufg closes at ${ACHIEVED} MHz (target ${TARGET_MHZ} MHz)"
if awk "BEGIN{exit !($ACHIEVED < $TARGET_MHZ)}"; then
    echo "TIMING FAILED: ${ACHIEVED} MHz < ${TARGET_MHZ} MHz target." >&2
    echo "  The bridge's own counters will corrupt above their closing frequency," >&2
    echo "  quietly and only at large counts.  Do not measure with this bitstream." >&2
    echo "  Critical path is in $OUT/pnr.log.  Set ALLOW_SLOW=1 to build anyway." >&2
    [ "${ALLOW_SLOW:-0}" = "1" ] || exit 1
    echo "  ALLOW_SLOW=1: continuing with a route that missed the target." >&2
fi
# MIN_MHZ is the floor ALLOW_SLOW cannot argue with.  TARGET_MHZ is an ambition
# -- routes land where they land, and 93 MHz is a perfectly good bitstream to
# measure at 50 MHz even though it missed a 100 MHz target.  What must never be
# waived is the margin over the clock the board will ACTUALLY run at: set
# MIN_MHZ to a comfortable multiple of that and the "quietly wrong at large
# counts" failure stays impossible regardless of who passes ALLOW_SLOW.
MIN_MHZ=${MIN_MHZ:-0}
if awk "BEGIN{exit !($ACHIEVED < $MIN_MHZ)}"; then
    echo "FLOOR FAILED: ${ACHIEVED} MHz < MIN_MHZ ${MIN_MHZ} MHz." >&2
    echo "  This floor is not waivable by ALLOW_SLOW.  No bitstream written." >&2
    exit 1
fi

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
echo "BD_DSP=${BD_DSP:-1}"
echo "BD_RLOC=${BD_RLOC:-v2}"
echo
echo "build_bench.sh PASS"
