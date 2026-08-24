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
# ---------------------------------------------------------------------------
# RULE A IS THE OUTER LOOP, AND IT BELONGS IN THE DEFAULT PATH.
#
# Until this existed, a bare `./hw/build_bench.sh <kernel>` derived rule E
# fresh (the converge.sh handoff just below) but never derived rule A.  It
# only APPLIED build/gen/<top>_sizes.vh if some earlier run happened to leave
# one there.  So a clean tree built every matched delay at bdc/emit.py's
# unmeasured estimate -- correct, but 2-4x longer than the route needs -- and
# the only way to get a tightened part was to know hw/tighten_loop.sh existed
# and run it by hand.  An optimisation you have to know about is one that does
# not get applied.
#
# WHY RULE A WRAPS RULE E AND NOT THE OTHER WAY ROUND.  Rule E measures how
# far a select's control input has to be padded to trail its data, and it
# measures that on a placed, routed design.  Rule A changes the length of the
# matched-delay chains, which changes placement, which changes every number
# rule E just measured.  Run rule E outside and its pads are stale the moment
# rule A moves a chain.  Run rule A outside -- one converged rule E build per
# rule A iteration -- and each set of pads is measured against the chain
# lengths that will actually ship.  That is why this block sits ABOVE the
# converge.sh handoff rather than below it.
#
# THE GUARDS, in the order they are tested:
#
#   BD_TIGHTEN_RUNNING   set by hw/tighten_loop.sh on every build it drives.
#                        This is the recursion guard: without it this block
#                        would re-enter the loop that invoked it, forever.
#   BD_SIZES             any explicit value -- a path, or "none" -- means the
#                        caller has already decided which sizes to build with,
#                        so deriving a fresh set would throw that away.
#   BD_NO_TIGHTEN=1      the untightened escape hatch.  It already skipped
#                        rule E; it now skips rule A too, which is both what
#                        the name says and what the same variable means in
#                        flow.sh.
#   --null               the null DUT has no delay-bearing cells to size.
#
# Anything else is the default, and the default is now tightened.
if [ -z "${BD_TIGHTEN_RUNNING:-}" ] && [ -z "${BD_SIZES:-}" ] \
   && [ "${BD_NO_TIGHTEN:-0}" != "1" ] && [ "$NULL" != "1" ]; then
    echo "build_bench.sh: MODE=tighten -- no BD_SIZES, no BD_NO_TIGHTEN;" \
         "deriving per-route matched-delay sizes for $TOP by running" \
         "hw/tighten_loop.sh (rule A outer, rule E inner)" >&2
    exec env BD_TIGHTEN_RUNNING=1 "$(dirname "$0")/tighten_loop.sh" \
        "$KERNEL" "${BD_TIGHTEN_ITERS:-6}"
fi

# --null skips this branch for the same reason it skips MODE=tighten above,
# and the reason is measured rather than assumed: verify/skew.py on
# collatz64_null_bench_gen reports "0 select gates, 0 measured, 0 violated"
# and converge.sh writes an empty pads.json.  There is nothing in a null DUT
# to pad.  Without this the null control ran the full rule E search anyway --
# up to 6 complete place-and-route builds to discover an empty set -- and on
# collatz64 and xorshift that overran the per-seed PnR timeout and reported
# as a BUILD FAILURE, which is how two null controls sat without a bitstream.
if [ -z "${BDC_SELECT_PADS:-}" ] && [ "${BD_NO_TIGHTEN:-0}" != "1" ] \
   && [ "$NULL" != "1" ]; then
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
elif [ "$NULL" = "1" ]; then
    # Reachable only since --null stopped being handed to converge.sh above.
    # It is not a re-entry, so BDC_SELECT_PADS is unset and naming it here
    # under `set -u` aborts the build -- which is exactly what happened.
    echo "build_bench.sh: MODE=null -- building $TOP directly; a null DUT" \
         "has no delay-bearing cells and no select gates to size" >&2
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

# The per-route matched-delay sizes, when a previous build of THIS top has
# produced them.  verify/tighten.py --emit writes one `define BD_SZ_<path>
# per delay-bearing cell, and build/gen/<top>.v declares each of those under
# `ifndef with the kernel's own default -- so this file, read first, wins, and
# its absence leaves the circuit exactly as it was.
#
# BD_SIZES=none forces the unsized build, which is what you want when you are
# producing the SDF that the next set of sizes will be measured from: sizes
# belong to one route, and a route built from sizes is not the route they were
# measured on.  hw/tighten_loop.sh drives that alternation.
SIZES=build/gen/${TOP}_sizes.vh
# BD_SIZES may name a file to build with.  Before this, BD_SIZES was only ever
# compared against "none", so BD_SIZES=/some/other/sizes.vh silently built with
# build/gen/<top>_sizes.vh -- the caller's file was read as "not none" and then
# ignored.  A wrong-but-plausible build is worse than a refused one.
if [ -n "${BD_SIZES:-}" ] && [ "${BD_SIZES}" != "none" ] \
   && [ "${BD_SIZES}" != "auto" ]; then
    if [ ! -e "${BD_SIZES}" ]; then
        echo "build_bench.sh: BD_SIZES=${BD_SIZES} does not exist" >&2
        exit 1
    fi
    SIZES="${BD_SIZES}"
fi
SRCS="rtl/*.v build/gen/${KERNEL}_kernel_bench.v build/gen/${TOP}.v"
if [ "${BD_SIZES:-auto}" != "none" ] && [ -e "$SIZES" ]; then
    SRCS="$SIZES $SRCS"
    echo "build_bench.sh: applying $(grep -c '^`define' "$SIZES") measured " \
         "delay size(s) from $SIZES" >&2
else
    echo "build_bench.sh: no measured sizes applied -- every chain at " \
         "bdc/emit.py's unmeasured estimate" >&2
fi

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

# And write the answer down beside the SDF, exactly as build_hw.sh does.
# This file was missing here, and it is not cosmetic: verify/tighten.py prints
# "toolchain UNSTAMPED" without it, and everything hw/tighten_loop.sh does
# depends on the sizes it emits belonging to a KNOWN binary.  Placement is
# deterministic per nextpnr build and not stable across builds, so a size
# measured under one binary and applied under another is not a measurement.
# Memory records fasm.cc being reverted underneath a session mid-run; that is
# the failure this stamp catches.  First line names nextpnr because tighten.py
# quotes the first line matching that word.
mkdir -p "$OUT"
{
    printf 'nextpnr %s  %s\n' \
        "$(sha256sum "$NEXTPNR" | cut -c1-16)" "$NEXTPNR"
    "$(dirname "$0")/../verify/toolchain.sh" "$NEXTPNR" 2>&1
} > "$OUT/toolchain.txt" || true

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
# 83.3 MHz, not 100.  This harness does not close 100 MHz and asking it to
# made the DEFAULT build path fail out of the box, for a reason that has
# nothing to do with what it was failing about: six seeds land at 79.6-97.7
# MHz, so the best of them still misses 100 and the build refuses.  The path
# is 94% routing in the bridge's bctrl_rst net -- it is the harness, not the
# kernel, and no amount of tightening moves it.
#
# 83.3 MHz is also simply the truth about how these parts are measured: the
# PS drives them at CLK_CTRL=0x00100C00, which is 83.3 MHz.  Building for a
# clock faster than the one the board supplies bought nothing and cost every
# default build.  Raise it deliberately with TARGET_MHZ= if you have a reason.
TARGET_MHZ=${TARGET_MHZ:-83}

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
        # Last seed, and it failed -- but "the last attempt failed" is not "every
        # attempt failed".  collatz64_null routed at 85.52 MHz on seed 3 and then
        # lost seeds 4, 5 and 6 to the timeout; this branch threw that route away
        # and reported "PNR FAILED on all 6 seeds", which was simply untrue.  If
        # an earlier seed banked a route, fall through to the restore below and
        # use it.
        if [ -e "$OUT/$TOP.fasm.best" ]; then
            echo "PNR FAILED on the last seed, but seed(s) earlier in this run routed at ${BEST} MHz -- using the best banked route." >&2
            ACHIEVED="$BEST"
            break
        fi
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

# If measured sizes were applied, PROVE they hold on the route this build
# actually got, before anyone can program the result.
#
# This gate exists because a sizes file is NOT portable and measurement says so
# loudly.  Same 12 sizes, same design, five nextpnr seeds:
#
#   default  clean     seed 11  clean     seed 22  clean
#   seed 33  ucmpi0 short by 229 ps       seed 44  (rule E did not converge)
#
# and after raising ucmpi0, seed 33 instead reported uaddi0 short by 557 ps.
# Every seed finds a DIFFERENT cell, because a matched delay's own per-element
# cost depends on how its chain got placed -- see cells/hw/tighten_loop.sh.
# So the sizes belong to one route, exactly as verify/tighten.py's emitted
# header says, and a stale or borrowed sizes file will build happily and be
# short somewhere.  Short is the direction that is silent PVT corruption
# rather than a simulation failure, so this must not be a warning.
#
# Rule A only.  tighten.py's exit code also carries rule D, the one-sided
# select screen that fires on every bd_steer before anything is tightened.
# BD_SIZES_GATE=0 is for hw/tighten_loop.sh ONLY.  That loop deliberately
# builds sizes it expects to fail, because tighten.py prices the correction
# off the failing route (verify/tighten.py:1020) and the next iteration
# needs that number.  The loop runs this same rule A check itself and only
# keeps a build that passes, so nothing escapes ungated -- but if this gate
# fired there it would turn the loop's feedback signal into a build error
# and the loop could never converge.  Do not set it anywhere else.
if [ "${BD_SIZES:-auto}" != "none" ] && [ "${BD_SIZES_GATE:-1}" = "1" ] \
   && [ -e "$SIZES" ]; then
    echo
    echo "== measured sizes: re-checking rule A on the route this build got =="
    python3 "$(dirname "$0")/../verify/tighten.py" "$OUT/$TOP.sdf" \
        > "$OUT/tighten_gate.log" 2>&1 || true
    NVIOL=$(awk '/^A\. /{a=1;next} /^B\. /{a=0} a' "$OUT/tighten_gate.log" \
            | grep -c "VIOLATION" || true)
    if [ "${NVIOL:-0}" -ne 0 ]; then
        echo "SIZES REJECTED: $NVIOL cell(s) whose request does not trail their" >&2
        awk '/^A\. /{a=1;next} /^B\. /{a=0} a' "$OUT/tighten_gate.log" \
            | grep "VIOLATION" | head -5 | sed 's/^/  /' >&2
        echo "  own datapath ON THIS ROUTE.  $SIZES was measured somewhere else." >&2
        echo "  Re-derive it here:  hw/tighten_loop.sh ${TOP%_bench_gen}" >&2
        echo "  or build without it: BD_SIZES=none $0 ${TOP%_bench_gen}" >&2
        echo "  No bitstream written." >&2
        rm -f "$OUT/$TOP.bit"
        exit 1
    fi
    echo "rule A holds on this route for all $(grep -c '^`define' "$SIZES") measured size(s)"
fi

echo "BD_DSP=${BD_DSP:-1}"
echo "BD_RLOC=${BD_RLOC:-v2}"
echo
echo "build_bench.sh PASS"
