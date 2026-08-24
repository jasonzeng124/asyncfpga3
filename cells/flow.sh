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

# build/pnr/soak.sdf is verify/tighten.py's INPUT.  Every artifact below is
# named soak.*, so building a different design here would overwrite the gate's
# SDF with one from another design and the next tighten run would silently
# audit the wrong thing.  BD_OUT redirects the whole tree; a generated top must
# set it, and is refused below if it does not.
OUT=${BD_OUT:-build/pnr}
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

# Measured delay lengths are the DEFAULT now, not opt-in: a bare ./flow.sh
# derives them itself by running verify/resize.sh fresh and building with
# whatever it settles on.  BD_SIZES=<file> is still the explicit override --
# unchanged, and it still wins over everything else, because bdc/ and the
# other gates that generate their own top depend on naming an exact file.
# BD_NO_TIGHTEN=1 is the escape hatch back to the placeholder build.
#
# Exactly one of those three runs, and it is announced loudly, because the
# whole point of the gates is that you always know which design you just
# checked:
#
#   BD_SIZES=<file>   explicit file, as before.
#   BD_NO_TIGHTEN=1   the untightened placeholders in verify/soak_top.v.
#   (neither)         run verify/resize.sh fresh, then build with its answer.
#
# What must NEVER happen is silently picking up a sizes.vh that merely
# happens to be lying in $OUT from some earlier run (teeth.sh's own sabotage
# file has sat in build/pnr/sizes.vh before now) -- that would mean a bare
# ./flow.sh sometimes means one design and sometimes another with no visible
# difference.  The fix is to RUN THE LOOP FRESH every time the default path
# is taken, never to read $OUT/sizes.vh back as an input; the copy into
# $OUT/sizes.vh below is a RECEIPT of what this build used, not a cache.
#
# BD_TIGHTEN_RUNNING is resize.sh's own recursion guard: it always exports
# BD_SIZES before it calls back into this script (see verify/resize.sh), so
# the BD_SIZES branch below already keeps this from recursing.  The check
# just below is belt-and-braces in case that ever stops being true.
if [ -n "${BD_TIGHTEN_RUNNING:-}" ] && [ -z "${BD_SIZES:-}" ]; then
    echo "flow.sh: BD_TIGHTEN_RUNNING is set but BD_SIZES is not -- this should"
    echo "         be impossible (resize.sh always exports BD_SIZES before it"
    echo "         calls back into flow.sh).  Refusing to recurse into"
    echo "         verify/resize.sh again."
    exit 2
fi

SIZES=""
if [ -n "${BD_SIZES:-}" ]; then
    [ -f "$BD_SIZES" ] || { echo "BD_SIZES=$BD_SIZES does not exist"; exit 2; }
    cp "$BD_SIZES" "$OUT/sizes.vh"
    SIZES="-DBD_SIZES -I$OUT"
    echo "MODE: explicit -- using measured delay lengths from BD_SIZES=$BD_SIZES"
elif [ "${BD_NO_TIGHTEN:-0}" = "1" ]; then
    echo "MODE: BD_NO_TIGHTEN=1 -- using the UNTIGHTENED placeholder delay" \
         "lengths in verify/soak_top.v"
else
    echo "MODE: default -- no BD_SIZES, no BD_NO_TIGHTEN; deriving tightened" \
         "lengths by running verify/resize.sh fresh"
    echo
    if ! BD_TIGHTEN_RUNNING=1 ./verify/resize.sh; then
        echo
        echo "flow.sh: verify/resize.sh did not settle -- see ${BD_OUT:-build}/resize/" \
             "for its logs."
        echo "         Use BD_NO_TIGHTEN=1 for the untightened placeholder" \
             "build, or"
        echo "         BD_SIZES=<file> to supply lengths explicitly."
        exit 1
    fi
    # Follows BD_OUT with verify/resize.sh, so two designs cannot read each
    # other's settled lengths.
    RESIZED=${BD_OUT:-build}/resize/sizes.vh
    [ -f "$RESIZED" ] || {
        echo "flow.sh: verify/resize.sh reported success but $RESIZED is missing"
        exit 2
    }
    cp "$RESIZED" "$OUT/sizes.vh"
    SIZES="-DBD_SIZES -I$OUT"
    echo
    echo "MODE: default -- verify/resize.sh settled; building with the" \
         "derived lengths in $RESIZED"
fi

# The design under test is OPT-IN too, via BD_TOP_V=<file> BD_TOP_M=<module>,
# and for the same reason as BD_SIZES above: bdc/ generates tops and runs them
# through these gates, and a bare ./flow.sh must keep meaning the hand-written
# soak design no matter what is lying around in build/.  The two pins in
# soak.xdc are the board's, so a generated top has to present pin_in/pin_out
# as well -- that is a constraint on the generator, not something to relax
# here.
TOP_V="${BD_TOP_V:-verify/soak_top.v}"
TOP_M="${BD_TOP_M:-soak_top}"
if [ "$TOP_V" != "verify/soak_top.v" ]; then
    [ -f "$TOP_V" ] || { echo "BD_TOP_V=$TOP_V does not exist"; exit 2; }
    if [ -z "${BD_OUT:-}" ]; then
        echo "BD_TOP_V is set but BD_OUT is not."
        echo "Everything this script writes is named soak.*, and"
        echo "build/pnr/soak.sdf is verify/tighten.py's input.  Building a"
        echo "generated top into the default tree would overwrite the gate's"
        echo "SDF with a different design's, and the next tighten run would"
        echo "audit that one without saying so.  Set BD_OUT=build/pnr/<name>."
        exit 2
    fi
    echo "using the generated top $TOP_V (module $TOP_M) -> $OUT"
fi

# DSP48E1 is ON.  It was OFF for a long stretch on a measured toolchain
# fault; that fault is now root-caused and patched, and the "before" numbers
# below are what it looked like while the cause was still open.
#
# It was off from the initial commit as a blanket "infer no hard blocks" at a
# time when no kernel had a multiply in it at all.  kernels/ipow gave the
# question its first real subject, and on area and bundling the DSP won:
# ipow drops from 3572 to 1452 occupied LUT sites, 61% off, and rule E
# (verify/skew.py) goes from 5 of 24 select gates violated to 0 of 24.  On
# that evidence it was turned ON.  Then it went to the board.
#
# THE DSP PATH COMPUTED THE WRONG PRODUCT ON THIS BOARD.  (Historical --
# see the fix below.)
#
#   kernels/ipow, 2016 vectors through hw/xsdb_ipow_sweep.tcl, same RTL,
#   same harness, same seed:
#       BD_DSP=1   965 of 2016 correct
#       BD_DSP=0  2016 of 2016 correct
#
#   hw/mult_ps.v reduces that to a design whose entire datapath is
#   `assign o_data_pl = a_data_reg * b_data_reg;` -- no kernel, no handshake
#   around the multiply, no matched delay, operands written by the host and
#   the product read back milliseconds later:
#       BD_DSP=1    25 of 430 correct
#       BD_DSP=0   430 of 430 correct
#
#   That build lets yosys absorb the operand registers into the DSP (AREG=1).
#   Building it with -DBD_KEEP_OPERANDS blocks the absorption, giving AREG=0 --
#   the configuration kernels/ipow produces -- and it is broken too, 205 of
#   430, but breaks DIFFERENTLY: small operands come back as 0 rather than as
#   a corrupted product.  Two configurations, two wrong behaviours, one `*`.
#
#   1 * 4294967295 returns 0x0001FFFF: the low 17 bits and nothing else.
#   The cascade's high partial products are not reaching the output.
#
# WHERE IT WAS NOT.  Not the compiler: bdc/simcheck.py passes ipow, including
# (7,11), which the board got wrong.  Not synthesis: the post-yosys netlist
# for a bare 32x32 multiply, simulated against the toolchain's own
# cells_sim.v, is right on 4007 of 4007 vectors including every operand the
# board failed.  Not bundled-data timing: BD_MUL_SCALE=4 lengthens the
# matched delay from 64 links to 256 and the design got WORSE, 921 of 2016,
# with the failing set moving -- a delay that was short cannot be made short
# by making it longer.  verify/tighten.py independently reported +10.7 ns of
# margin on that path, and the routed SDF did carry the cascade arcs (A->P
# 5400 ps, PCIN->P 1710 ps) for it to have crossed.
#
# So the fault was between the correct netlist and the bitstream -- the same
# seam as patches/nextpnr-xilinx-lut-pinmap.patch, which was 131 LUTs written
# into the bitstream disagreeing with the netlist that produced them.
#
# WHAT WAS CHECKED AT THAT SEAM, and found CORRECT: placement (the three
# cascaded DSPs land on DSP48_X0Y20/21/22, adjacent sites in one column, as
# the PCOUT->PCIN cascade requires); OPMODE (decoded from the routed
# netlist, the cascade asks for Z=000 at the head, Z=101 in the middle,
# Z=001 at the tail -- a correct 32x32 decomposition -- and the FASM's
# inversion bits matched that cell for cell); and ALUMODE, INMODE, the
# operand slices, and "the constant network (VCC, so the inversion bits mean
# what the decode above assumed)".  That last clause was the trap: the
# inversion bits for these particular pins were never being read from the
# parameter they were actually stored under, so "VCC, therefore correct"
# was checking that a bit existed, not that it was the right bit.
#
# ONE REAL DISAGREEMENT WAS FOUND ALONG THE WAY, and it was not the cause:
# patches/nextpnr-xilinx-dsp-areg.patch.  prjxray defines the DSP feature
# AREG_2_ACASCREG_1 as the conjunction (AREG == 2 && ACASCREG == 1); fasm.cc
# derived its Z-form bit from ACASCREG alone, so AREG=1 -- what yosys emits
# whenever it absorbs one level of input register into the multiply -- wrote
# no bit and read back on silicon as AREG=2.  With the patch the bit appears
# and the board result was BIT-IDENTICAL, because a design that reads its
# answer milliseconds later cannot see an extra input pipeline stage.  Worth
# having, not the bug.
#
# THE ACTUAL CAUSE: patches/nextpnr-xilinx-dsp-constpins.patch.  A set of
# DSP48E1 site pins -- INMODE0..4, ALUMODE2, ALUMODE3, OPMODE6 among them --
# have no interconnect path into the site at all; prjxray gives them a value
# only through a tile-local constant bit.  nextpnr's packer left three of
# those pin groups out of the const-pin list ("TODO: these seem to be
# inverted for unknown reasons"), so they were never wired to a constant net
# and no FASM bit was ever emitted for them -- no error, no warning, just
# the tile default on silicon.  INMODE came up 11111 instead of 00000, and
# per UG479 Table 1-11, INMODE[1]=1 gates the multiplier's A input to zero:
# the DSP ignored A entirely and returned near-constant junk, with a correct
# netlist and clean timing the whole way down.  The "seem to be inverted"
# TODO was half right -- these pins do bypass the site's input inverter, so
# a naive fix (just uncomment them) makes it worse, not better.  The other
# half of the fix, in fasm.cc, is a parameter-name lookup that stripped
# digits from a pin name before checking whether the netlist wanted it
# inverted, so it always missed and always chose the un-flipped constant.
# See patches/README.md for the full mechanism.
#
# Same rig, same RTL, patched toolchain:
#
#   bit-walk, all 16 A bits x 2 DSPs        : A had zero effect -> all correct
#   mult2_ps, two lone 16x16, 415 vectors   : 1/315, 315/315 -> 415/415, 415/415
#   mult_ps, 32x32 three-DSP cascade        : 25/430 -> 430/430
#   ipow_ps, real kernel, 2016 vectors      : 965/2016 -> 516/516
#
# BD_DSP=0 is kept as an escape hatch (bisecting a future toolchain change,
# comparing area against the LUT-only path) but is no longer the default.
DSPOPT="-nodsp"
[ "${BD_DSP:-1}" = "1" ] && DSPOPT=""

echo "== synthesis =="
"$YOSYS" -p "
read_verilog -lib -specify $CELLS_SIM
read_verilog $SIZES rtl/*.v $TOP_V
synth_xilinx -family xc7 -flatten $DSPOPT -nosrl -nolutram -nobram -noclkbuf -top $TOP_M
write_json $OUT/soak.json
stat
" > $OUT/synth.log 2>&1 || { echo "SYNTH FAILED"; tail -30 $OUT/synth.log; exit 1; }

# synth_xilinx prints its own statistics as well; only the last block is the
# final netlist.
last=$(grep -n "^=== $TOP_M ===" $OUT/synth.log | tail -1 | cut -d: -f1)
tail -n +"$last" $OUT/synth.log | grep -E "^\s+[0-9]+\s+(LUT|RAMB|IBUF|OBUF)" || true

lut_cells=$(tail -n +"$last" $OUT/synth.log \
            | grep -E "^\s+[0-9]+\s+LUT[1-6](_2)?$" \
            | awk '{s+=$1} END {print s+0}')
echo "yosys: $lut_cells LUT cells (a LUT6_2 counts once -- it is one site)"

# Relative placement, same as hw/build_hw.sh.  soak_top is built from the same
# bd_link/bd_pipe/bd_mux/bd_steer primitives every kernel is, so it wants the
# same RLOC_GROUP clustering -- without it the C node of a link or pipe stage
# lands nanoseconds of interconnect from its own latch and rule E fails here
# while passing on every kernel, which is a difference in the FLOW rather than
# in the design.  soak_top's own storage is a bd_pipe (verify/soak_top.v's
# `upipe`), not a bd_link, and it is not named `ulink_...` the way a compiled
# kernel's is -- hw/rloc_stamp.py's controller regex keys off the `ctl.u.u` /
# `many.cpair[N].u.u` / `many.codd.u.u` suffix alone for exactly this reason.
# The cluster floats; nothing is pinned.  BD_RLOC=none turns it off.
BD_RLOC=${BD_RLOC:-v2}
if [ "$BD_RLOC" != none ]; then
    python3 hw/rloc_stamp.py $OUT/soak.json $OUT/soak.rloc.json \
        --variant "$BD_RLOC" --report > $OUT/rloc.log 2>&1 || {
            echo "RLOC STAMP FAILED"; cat $OUT/rloc.log; exit 1; }
    mv $OUT/soak.rloc.json $OUT/soak.json
    grep -E "group|link" $OUT/rloc.log | tail -3
fi

echo
echo "== toolchain =="
# Which binary is about to produce these numbers.  Three of this project's four
# bugs were BITSTREAM bugs -- clean netlist, clean timing, wrong bits -- so the
# patch set is part of the measurement, not background to it.  See
# verify/toolchain.sh for the day this was learned the expensive way.
./verify/toolchain.sh "$NEXTPNR"

echo "== place and route =="
# Every routed number produced below -- occupied LUT sites, the SDF arrival
# times, and every margin verify/tighten.py derives from them -- belongs to the
# nextpnr build that produced it, and nothing else here recorded which one that
# was.  This is a receipt, not a knob: there is exactly ONE installed
# toolchain, deliberately, because maintaining parallel ones costs more than it
# saves.  What that buys instead is that an update SUPERSEDES old numbers
# rather than making them comparable -- so a saved margin is only meaningful
# next to the version that measured it.  nextpnr's version string carries the
# git hash (e.g. 0.9.1-17-g69119066), so this names the exact commit.
#
# This project has already been bitten three times by nextpnr placer/packer
# defects, once by one that was fixed upstream 94 commits ahead of the
# installed build.  Expect the toolchain to move; the stamp is what keeps the
# numbers honest when it does.
"$NEXTPNR" --version > $OUT/toolchain.txt 2>&1
"$YOSYS" -V >> $OUT/toolchain.txt 2>&1
sed 's/^/  /' $OUT/toolchain.txt

# --sdf is what verify/tighten.py reads: real per-net routed delays, which is
# the only place the matched-delay lengths can come from.
"$NEXTPNR" --chipdb "$CHIPDB" --xdc $OUT/soak.xdc --ignore-loops \
           --json $OUT/soak.json --write $OUT/soak_routed.json \
           --sdf $OUT/soak.sdf --fasm $OUT/soak.fasm > $OUT/pnr.log 2>&1 \
    || { echo "PNR FAILED"; tail -40 $OUT/pnr.log; exit 1; }

echo "routed."
echo

# The FASM is the netlist as the bitstream sees it.  prjxray writes ONE 64-bit
# xLUT.INIT per occupied LUT site: the O6 function in the upper half, the O5
# function in the lower.  So LUT.INIT lines ARE occupied sites, and that is
# what gets reported here.
#
# Do not try to match these INITs against the constants in verify/inits.py.
# The packer permutes LUT input pins freely and rewrites INIT to match, so the
# bits are a different -- equivalent -- constant.  The constants are proved
# exhaustively at the source, which is where they mean something.
lut_sites=$(grep -c "LUT\.INIT" $OUT/soak.fasm || true)
brams=$(grep -c "RAMB18" $OUT/soak.fasm || true)
echo "FASM:  $lut_sites occupied LUT sites, $brams BRAM lines"

# Whether the fractured pairs held is checked against the routed netlist, by
# comparing the two halves' BELs directly.  It used to be inferred from the
# site count above running ahead of $lut_cells, and that proxy gave a false
# FAIL on the first design with many constants in it: nextpnr inserts its own
# LUTs to drive constant nets ($PACKER_GND_NET / $PACKER_VCC_NET), 736 of them
# on gcd, and those are sites the design did not ask for.  Every pair had in
# fact held.  verify/fracture.py checks the claim instead of a proxy for it.
python3 verify/fracture.py $OUT/soak_routed.json || exit 1

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
