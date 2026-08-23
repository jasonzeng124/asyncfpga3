#!/usr/bin/env bash
# Build a hardware design all the way to a loadable bitstream.
#
#   hw/build_hw.sh ro_top
#
# flow.sh stops at FASM because the place-and-route gate does not need a
# bitstream -- it needs the routed SDF, which is the thing delay sizing reads.
# This goes the rest of the way, because a measurement needs something to load.
#
# Two rules from flow.sh are DELIBERATELY not carried over here:
#
#   the "no global clock buffer in the bitstream" check.  In the library a BUFG
#   on a manufactured clock is a two-nanosecond error hiding on a path a
#   matched delay was sized against.  Here the BUFGs are the instrument: a ring
#   has to reach a counter's clock pin and nothing else on this part will carry
#   it.  They are explicit, they are counted below, and if the number moves
#   the design changed.
#
#   the fractured-pair site check.  Nothing here is fractured.
#
# What IS carried over: --ignore-loops, because a ring oscillator is a
# combinational loop and so is every C-element in the library.
set -eu

cd "$(dirname "$0")/.."

TOP=${1:-ro_top}

# Default build path: tighten.  A bare hw/build_hw.sh <design> hands off to
# verify/converge.sh, which iterates this same build (via BDC_SELECT_PADS) to
# a fixed point on rule E's select-vs-request margins -- see converge.sh's
# header for why a constant pad measurably does not work and a per-link,
# measured one does.
#
# BDC_SELECT_PADS already being set is the re-entry signal: converge.sh sets
# it (even to build/converge/<design>/pads.json holding '{}' on iteration 1)
# before every build_hw.sh call it makes, so seeing it set here means
# converge.sh is the one calling, not a human -- just build.  BD_NO_TIGHTEN=1
# is the escape hatch back to bdc/emit.py's own unmeasured SELECT_PAD=4
# estimate on every channel, no convergence loop at all.
#
# ro_top, arb_mtbf and arb_prot instantiate no bd_link/bd_pipe-fed bd_steer
# or bd_mux (see the *) case below -- they sit directly on rtl/bd_latch.v,
# rtl/bd_ce.v and rtl/bd_arb.v), so they have no select gates for rule E to
# measure.  verify/skew.py already reports that as "0 select gates ... 0
# measured, 0 violated" and returns 0 without walking anything (it only
# walks per select gate found), and converge.sh already treats a
# zero-deficit first measurement as CONVERGED.  So routing one of these
# three through converge.sh below costs exactly the one build it would have
# cost anyway, and still ends in "CONVERGED", not an error -- nothing extra
# to make that true.
if [ -z "${BDC_SELECT_PADS:-}" ] && [ "${BD_NO_TIGHTEN:-0}" != "1" ]; then
    echo "build_hw.sh: MODE=converge -- no BDC_SELECT_PADS (not a re-entry)" \
         "and no BD_NO_TIGHTEN; handing off to verify/converge.sh for $TOP" >&2
    exec "$(dirname "$0")/../verify/converge.sh" "$TOP"
fi
if [ "${BD_NO_TIGHTEN:-0}" = "1" ]; then
    echo "build_hw.sh: MODE=BD_NO_TIGHTEN -- building $TOP directly, select" \
         "channels at bdc/emit.py's unmeasured SELECT_PAD estimate" >&2
else
    echo "build_hw.sh: MODE=converge re-entry (BDC_SELECT_PADS=$BDC_SELECT_PADS)" \
         "-- building $TOP" >&2
fi

# The source list, per design, spelled out rather than globbed -- the same
# reason flow.sh names its files.  ro_top, arb_mtbf and arb_prot each sit
# directly on a handful of primitives and read three files; gcd_hw is the
# first design here that instantiates a whole COMPILED kernel, so it needs
# the entire library plus two files that are not hand-written:
#
#   ../build/gen/gcd_kernel.v  generated, gitignored, and regenerated with
#       python3 -m bdc.emit build/frontend/gcd/comp/handshake_transformed.mlir \
#               --no-top -o build/gen/gcd_kernel.v
#       from the project root.  It is checked for below by name, because a
#       stale or missing kernel otherwise shows up as "module bdc_gcd not
#       found" a hundred lines into a yosys log.
#   hw/gcd_rig.v               the reset/vector/compare environment around it.
case "$TOP" in
gcd_hw)
    KERNEL=../build/gen/gcd_kernel.v
    SRCS="rtl/*.v $KERNEL hw/gcd_rig.v hw/$TOP.v"
    # Regenerated here rather than checked for, because hw/gcd_rig.v now
    # connects PROBE PORTS on bdc_gcd and those exist only if the kernel was
    # emitted with --probe.  A stale kernel would fail as "port probe_n138_req
    # does not exist", which is a true statement about a file nobody remembered
    # to regenerate -- so the build regenerates it and the two cannot drift.
    # BDC_PROBE names channels as they appear in the emitted Verilog; see the
    # probe-port block in bdc/emit.py, and gcd_rig.v's header for why %138.
    mkdir -p ../build/gen
    ( cd .. && python3 bdc/emit.py \
        build/frontend/gcd/comp/handshake_transformed.mlir \
        --no-top --probe n138,n136_u,n135__2 -o build/gen/gcd_kernel.v )
    ;;
multn_ps)
    # Eight independent one-DSP multiplies; see hw/multn_ps.v.
    SRCS="rtl/*.v hw/$TOP.v"
    ;;
mult2_ps)
    # Two independent one-DSP multiplies; see hw/mult2_ps.v.
    SRCS="rtl/*.v hw/$TOP.v"
    ;;
mult_ps)
    # No compiled kernel at all -- the datapath is one expression in the
    # bridge.  See hw/mult_ps.v.
    SRCS="rtl/*.v hw/$TOP.v"
    ;;
ro_link_ps)
    # Five bd_link rings of different lengths, one token each, counted against
    # FCLK0.  Needs the whole library, not the three-file primitive list the
    # default case gives: this is the first rig here built out of bd_link
    # itself rather than out of bd_latch/bd_ce directly.  See hw/ro_link_ps.v.
    SRCS="rtl/*.v hw/$TOP.v"
    ;;
ipow_ps)
    # ipow is the kernel with the variable x variable multiplies, so it is
    # the one that actually infers DSP48E1 -- and therefore the one whose
    # numbers move when BD_DSP does.  It is ON by default now; see the BD_DSP
    # block below.  Nothing else differs from the gcd_ps case.
    KERNEL=../build/gen/ipow_kernel_ps.v
    SRCS="rtl/*.v $KERNEL hw/$TOP.v"
    mkdir -p ../build/gen
    ( cd .. && python3 bdc/emit.py \
        build/frontend/ipow/comp/handshake_transformed.mlir \
        --no-top -o build/gen/ipow_kernel_ps.v )
    ;;
gcd_ps|gcd_bench)
    # The PS7-driven harness: same compiled kernel as gcd_hw, but the vectors
    # come from the host over M_AXI_GP0 instead of a 16-entry case statement.
    # No --probe here -- hw/gcd_ps_top.v connects only the kernel's declared
    # channels, so a plain emit is what it expects.
    KERNEL=../build/gen/gcd_kernel_ps.v
    SRCS="rtl/*.v $KERNEL hw/$TOP.v"
    mkdir -p ../build/gen
    ( cd .. && python3 bdc/emit.py \
        build/frontend/gcd/comp/handshake_transformed.mlir \
        --no-top -o build/gen/gcd_kernel_ps.v )
    ;;
*)
    SRCS="rtl/bd_latch.v rtl/bd_ce.v rtl/bd_arb.v hw/$TOP.v"
    ;;
esac

TC=${TC:-/home/jayjay/dev2/lib/fpgatoolchain}
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

OUT=build/hw/$TOP
mkdir -p "$OUT"

# shellcheck disable=SC2086
for f in "$YOSYS" "$NEXTPNR" "$CHIPDB" "$CELLS_SIM" "$CELLS_XTRA" \
         "$FASM2FRAMES" "$FRAMES2BIT" $SRCS; do
    [ -e "$f" ] || { echo "missing: $f"; exit 2; }
done

# Existing is not the same as correct.  The check above proves the binary is
# there; this one proves it is the PATCHED one.  A bitstream from an unpatched
# nextpnr looks exactly as plausible as a good one everywhere except silicon.
"$(dirname "$0")/../verify/toolchain.sh" "$NEXTPNR"

# And write the answer down beside the SDF.  verify/tighten.py looks for
# toolchain.txt there and says UNSTAMPED without it, which is the right
# complaint: placement is deterministic per binary but NOT stable across
# binaries -- an inert-looking nextpnr change moves it -- so a margin quoted
# without its build is a fact about a build, not about the design.
#
# The sha goes on the FIRST line and names nextpnr, because tighten.py quotes
# the first line matching "nextpnr" -- and every patch row below it matches
# that word too, so leaving the order to chance would stamp a patch filename
# where the build belongs.
mkdir -p "$OUT"
{
    printf 'nextpnr %s  %s\n' \
        "$(sha256sum "$NEXTPNR" | cut -c1-16)" "$NEXTPNR"
    "$(dirname "$0")/../verify/toolchain.sh" "$NEXTPNR" 2>&1
} > "$OUT/toolchain.txt" || true

# The only physical pins on this board.  A design with no ports at all gives
# the packer nothing to anchor, so the two LEDs stay even though nothing here
# is measured by looking at them.
cat > "$OUT/$TOP.xdc" <<'EOF'
set_property PACKAGE_PIN W14 [get_ports led_red]
set_property IOSTANDARD LVCMOS33 [get_ports led_red]
set_property PACKAGE_PIN W13 [get_ports led_green]
set_property IOSTANDARD LVCMOS33 [get_ports led_green]
EOF

echo "== synthesis =="
# cells_xtra.v carries BSCANE2 as a blackbox; cells_sim.v does not have it.
#
# DSP48E1 is ON, and this default was inverted on 2026-08-21 because the bug
# that justified turning it off is fixed.  The full argument and the numbers
# are in cells/flow.sh next to the same two lines: several DSP48E1 site pins
# have no interconnect path and get a value only from a tile-local constant
# bit, nextpnr left three of those groups unwired, and INMODE came up at the
# tile default gating the multiplier's A operand to zero.  That is
# patches/nextpnr-xilinx-dsp-constpins.patch, and verify/toolchain.sh gates
# on its presence, so a binary without it cannot silently build this.
#
# BD_DSP=0 remains the escape hatch for bisecting a future toolchain change.
# It is not a safety default any more: leaving it off costs LUT multipliers
# on every kernel that has a variable-by-variable multiply, ipow first.
DSPOPT="-nodsp"
[ "${BD_DSP:-1}" = "1" ] && DSPOPT=""

# synth_xilinx's map_luts stage normally ends with xilinx_dffopt, which folds
# any FF bit whose D input is constant under some control condition (e.g. a
# capture-mux bit fed by a compile-time-constant TAG nibble) into a per-bit
# synchronous set/reset on that condition, rather than leaving it on the
# register's own uniform clock-enable.  That is a legitimate area
# optimization in general, but on arb_mtbf it was confirmed (by diffing a
# pre-route netlist dump against ro_top's own, which has the same pattern and
# still routes) to fragment a single logical register -- the 48-bit BSCANE2
# shift register `sr` -- into two different CE nets, and nextpnr-xilinx's
# packer does not discover a resulting half-slice control-set clash until
# POST-ROUTE legalisation, i.e. after paying for a full route: "disagrees
# with its half-slice on 'is_ceused' -- control-set contention in the
# placement".  Splicing the map_luts stage manually (see synth_xilinx.cc for
# the exact xc7/non-abc9/non-widemux command sequence this reproduces) and
# skipping just that one pass took `sr` from 5 distinct CE nets to 1 and
# raised the seed pass rate from roughly 1-in-8 to roughly 1-in-2 -- real,
# not incidental, but not sufficient alone; see arb_mtbf.v's header for the
# rest (the async liveness sampler's width, trimmed for the same reason).
"$YOSYS" -p "
read_verilog -lib -specify $CELLS_SIM
read_verilog -lib $CELLS_XTRA
# BD_DEFINES passes -D flags through to the design sources only (not the
# vendor cell models).  Used by hw/mult2_ps.v's BD_KEEP_OPERANDS.
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

# Relative placement.  BD_RLOC=v2 (default) stamps an RLOC_GROUP attribute on
# the post-synthesis netlist so nextpnr keeps each bd_link's C node in the same
# SLICE as its own latch -- see hw/rloc_stamp.py and patches/README.md.  The
# cluster floats; nothing is pinned.  BD_RLOC=none turns it off, and that is
# the ONLY way to reproduce a pre-2026-08-21 route: routed placement is stable
# per binary but not across binaries, so numbers from the two are not
# comparable.  An unpatched nextpnr ignores the attribute silently, which is
# what verify/toolchain.sh above is for.
BD_RLOC=${BD_RLOC:-v2}
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
# Placement scatter decides whether the clock router can reach every counter
# from its BUFG, and six global buffers on this part is close enough to the
# limit that some placements simply do not route.  Seed iteration is the
# accepted cost here, same as it is for the rest of the xc7 flow.
#
# arb_mtbf specifically: even after removing xilinx_dffopt's CE-fragmenting
# of `sr` (see the synthesis step above) this design's dense, fixed-location
# BSCANE2 control logic (sr + hold + the liveness sampler, all in the tck
# domain, competing for the same handful of half-slices) still only routes
# on roughly half of seeds -- nextpnr-xilinx's packer does not discover a
# half-slice control-set clash until AFTER a full route, so a failing seed
# is a real "control-set contention in the placement" error, not noise. The
# pinned seed is checked for determinism (three clean rebuilds, three
# identical PASSes) every time it's picked; NEXTPNR_SEED overrides it, e.g.
# to re-run the sweep after an RTL change -- which invalidates the old pin,
# since it shifts the netlist enough to change which seeds route. Seed 0 was
# the pin through the ctrl_sticky control-channel addition; that change broke
# seed 0 and a re-sweep found seed 1. Adding the por_sr power-on-reset
# generator (widening every sticky latch from LUT2 to LUT3, see arb_mtbf.v)
# shifted the netlist again and broke seed 1 too; a 0-9 re-sweep found seeds
# 3 and 7. Widening por_sr from 4 to 24 bits (same file -- the 4-bit window
# turned out to be a distinct bug, too short for the delay chains driving
# the real sticky latches to settle after configuration, not just a seed
# issue) shifted the netlist again and broke both 3 and 7; a fresh 0-9
# re-sweep found seeds 0, 4, 8, 9, and seed 0 was checked for determinism
# (three clean rebuilds, three identical PASSes, identical FASM stats).
# Adding the Phase 1 population (24 more channels) and Phase 2 windowed
# counters (on all 6 existing channels) roughly doubled LUT usage (348 -> 837
# sites) and broke seed 0 (routing failure on the tck global clock this
# time, not is_ceused -- plain congestion from the size increase); a fresh
# 0-9 re-sweep found seeds 4, 5, 9. Seed 4 was checked for determinism first
# and looked fine, but its routed SDF turned out to have a NON-MONOTONIC
# depth ladder (depth 2's chain measured longer than depth 4's) -- a
# placement-dependent failure mode distinct from routability, only visible
# by actually computing depth_ps against the SDF, not from PnR passing.
# Seeds 5 and 9 were checked and both monotonic; seed 5 picked and checked
# for determinism (three clean rebuilds, three identical PASSes, identical
# FASM stats). Adding the Phase 2 negative control (winctrl, one more
# channel + a 5th hold_addr bit) shifted the netlist again and broke every
# other seed from the previous sweep; re-swept 0-9, only seed 5 still
# passed, re-verified deterministic and re-confirmed monotonic. Adding the
# depth-16 diagnostic (a chain-tap spatial-snapshot twin of ch[5], see
# arb_mtbf.v) broke seed 5; a fresh 0-9 sweep found only seed 5 again
# (coincidentally still routable), re-checked monotonic on both ladders.
# Adding the depth-8 twin alongside it broke seed 5 again; a 0-9 re-sweep
# found seeds 0 and 2 routable, but seed 0 failed the THRESHOLD ladder's
# monotonicity (width 6 measured shorter than width 4) -- first time both
# depth_ps AND floor_ps were checked on every candidate, not just depth_ps,
# per the lesson from seed 4's broken depth ladder earlier in this history.
# Seed 2 passed both ladders and was checked for determinism (three clean
# rebuilds, three identical PASSes, identical FASM stats).  Adding the width
# discriminator (two LUTs per anomaly channel plus a filtered sticky bit --
# see the WFILT note in arb_mtbf.v) broke seed 2, and this time EVERY seed
# 0-5 failed to route identically, on tck rather than on is_ceused: plain
# congestion, not seed luck.  A filtered twin of the Phase 2 window counters
# was tried first and was what caused it (~162 extra flip-flops in the tck
# domain); dropping back to filtered STICKY BITS ONLY -- which answer the
# question on their own, since the raw counters saturate in microseconds --
# brought it back under the routing limit at 1005 LUT sites.  A 0-17 sweep
# then found only seeds 2, 9, 11 and 12 routable, and of those only 12 has a
# monotonic THRESHOLD ladder (2, 9 and 11 all measure width 4 shorter than
# width 3).  Seed 12 was checked for determinism: three clean rebuilds, three
# identical PASSes, byte-identical FASM.  The .bit md5 does differ between
# runs -- that is a timestamp in the bitstream header, not placement drift;
# the FASM is the thing that must be stable and it is.
#
# Scaling the population from 24 to 192 instances (plus the filtered sticky
# readback words) broke seed 12; a re-sweep found seed 3.  Wiring the
# arbiters' rst pin to a real reset instead of 1'b0, then arming the
# detectors from a shift register ~17 ms after that reset releases (both in
# arb_mtbf.v), each shifted the netlist again; the final sweep for that pair
# left seeds 0, 4 and 12 routable, seed 4 failed the THRESHOLD ladder, and
# seed 0 was pinned.  Adding the population aggregate rate counters (two
# 192-input OR trees plus two window-latch/sync/counter chains, ~54 flops --
# see the PER-INSTANCE RATE note in arb_mtbf.v) shifted it once more.  The
# first cut aggregated the population with two 192-input OR reductions and
# cost 3064 LUT sites, routing on seed 3 alone; the reductions turned out to
# be unusable for a reason that has nothing to do with routing (abc
# re-decomposes them against the grant LUTs, so they glitch on ordinary
# arbitration -- see arb_mtbf.v) and were replaced by counters wired directly
# to two individual instances, which is 2745 sites.  Seeds 1, 4 and 5 all
# route and all three are monotonic on both ladders.  Widening the width
# discriminator from one link to two (WFILT, see arb_mtbf.v -- one link was
# measured on hardware to be too narrow to clear the structural overlap at
# every placement) added ~200 sites to 2943 and, unusually, made routing
# EASIER: 7 of 8 seeds pass, only 0 fails.  Seed 5 is pinned (depth
# 0/124/398/1336/2511/6471 ps, floor 124/398/672/946/1958/2432 ps) after
# three clean rebuilds with byte-identical FASM.  All 198 grant pairs land
# fractured but every one of them MOVED, so the grant_bels.json baseline was
# deleted and re-recorded -- an exposure measured on the previous build does
# not carry over to this one.
#
# Note that PnR passing is NOT sufficient -- check BOTH ladders against the
# routed SDF on every candidate before pinning one.  Two separate seeds in
# this history routed cleanly and were still unusable.
#
# TOP is POSITIONAL (see the top of this file): ./build_hw.sh arb_mtbf.
# TOP=arb_mtbf ./build_hw.sh silently builds ro_top instead, which is easy to
# miss because it passes -- and then the board gets programmed with a stale
# bitstream whose readback addresses mean something else entirely.
if [ "$TOP" = "arb_mtbf" ]; then
    SEED="--seed ${NEXTPNR_SEED:-5}"
else
    SEED=""
    [ -n "${NEXTPNR_SEED:-}" ] && SEED="--seed ${NEXTPNR_SEED}"
fi

# --freq, when asked for.  nextpnr defaults its target to 12 MHz, so an
# unqualified "PASS" says nothing -- it is a pass against a target nothing
# here runs at.  Most designs in this directory do not care, because the only
# clocked logic is a readback shift register.  ro_link_ps does: its lap
# counters are clocked BY THE RINGS, at whatever rate a 3-stage ring turns,
# and a counter that does not close undercounts silently.  Setting a target
# makes the router work for the margin instead of stopping at whatever it
# happened to get.  --timing-allow-fail keeps the build going so the report
# can be read; the verdict lives in the log, not in the exit code.
FREQOPT=""
[ -n "${NEXTPNR_FREQ:-}" ] && FREQOPT="--freq ${NEXTPNR_FREQ} --timing-allow-fail"

# shellcheck disable=SC2086
"$NEXTPNR" --chipdb "$CHIPDB" --xdc "$OUT/$TOP.xdc" --ignore-loops $SEED $FREQOPT \
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
echo
echo "build_hw.sh PASS"

# ---------------------------------------------------------------------------
# arb_prot (hw/arb_prot.v) -- 96 bd_arbiter instances, each with a four-phase
# server and two self-timed clients.  2962 occupied LUT sites, 62 global buffer
# lines, 192 LUT6_2 (both the state node and the grant node of every arbiter
# stay fractured -- hw/check_fracture.py covers both, see its NAME_RE).
#
# NO SEED IS PINNED FOR THIS DESIGN, and that is a result rather than an
# omission: the default and every seed 1-5 route, and three rebuilds at the
# default produced byte-identical FASM.  arb_mtbf needs a pinned seed because
# it packs ~200 arbiters plus six ladders plus wide counters against BSCANE2's
# fixed site and most seeds fail to route tck; arb_prot has no ladders and no
# CARRY4 counters beyond two, so it is simply not congested.  If that ever
# changes, sweep and pin here the way arb_mtbf's history above does.
#
# rtl/bd_arb.v was added to the read_verilog line for this design: arb_mtbf
# only instantiates bd_c2n_set (which lives in rtl/bd_ce.v), but arb_prot
# instantiates the whole bd_arbiter.  Unused modules cost nothing after -top.
