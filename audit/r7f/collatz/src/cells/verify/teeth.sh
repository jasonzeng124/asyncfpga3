#!/usr/bin/env bash
# Does the sizing gate have teeth?
#
# A gate that has never failed is not evidence, it is decoration.  This builds
# the design under test a second time with ONE cell's matched delay removed
# entirely -- DELAY(0), which bd_delay renders as a bare wire, so there is not
# even a chain left in the netlist to find -- routes it, and requires
# verify/tighten.py to CATCH it.
#
# That zero-length case is the one that matters.  An earlier version of the
# sizing pass discovered its work by looking for delay chains and silently
# skipped any cell that had none, which meant the one configuration guaranteed
# to violate the bundling constraint was the one configuration it could not
# see.  This script exists so that cannot come back.
#
# The delay is overridden through the same BD_SIZES mechanism verify/resize.sh
# uses, not by editing the source.  An earlier version rewrote soak_top.v with
# sed and stopped working the moment the parameter was written differently.
#
# WHICH CELL GETS SABOTAGED IS NOT HARDCODED, and that is the third time this
# script has been caught turning into a no-op.  It used to name soak_top's
# `umerge`.  Pointed at a generated top via BD_TOP_V there is no `umerge`, so
# it defined a macro no source file read, built an identical design, watched
# tighten.py correctly pass it, and announced that the sizing gate had no
# teeth.  The victim now comes from the design under test: whichever cell rule
# A audits with the deepest datapath, since that is the one with the most to
# lose and the least chance of trailing without help.
#
# And the no-op is now CHECKED rather than assumed.  A cell with a zeroed delay
# drops out of --list-audited (which lists only cells that still carry links),
# so if the victim is still there after the override, the override never
# reached the source and everything after it would be theatre.
set -u
cd "$(dirname "$0")/.."

OUT=build/teeth
mkdir -p $OUT

# The census has to come from a build of the real design.  check.sh has just
# made one, but run flow.sh anyway when it is missing so this is also a
# standalone gate.
if [ ! -f build/pnr/soak.sdf ]; then
    ./flow.sh > $OUT/pre.log 2>&1 || { echo "teeth: the design would not build"
                                       tail -20 $OUT/pre.log; exit 2; }
fi

python3 verify/tighten.py --list-audited > $OUT/before.txt 2>&1
read -r VICTIM_MACRO VICTIM_PATH _ < $OUT/before.txt || true
if [ -z "${VICTIM_MACRO:-}" ]; then
    echo "teeth: rule A audits no delay-bearing cell in this design, so there"
    echo "       is nothing to remove and this gate proves nothing.  That is a"
    echo "       broken design or a broken census, not a pass."
    cat $OUT/before.txt
    exit 2
fi
echo "teeth: removing the matched delay on $VICTIM_PATH ($VICTIM_MACRO)"

# Save whatever sizes the census build actually used, so the restore at the
# bottom can put back THAT design (explicit BD_SIZES, one cheap re-route)
# instead of falling through to flow.sh's own default and re-running the
# whole verify/resize.sh sweep a second time just to undo a sabotage.
# build/pnr/sizes.vh is flow.sh's receipt of what it built with; it exists
# whenever the census build was tightened (explicit or default) and is
# absent for a BD_NO_TIGHTEN=1 census, which the fallback below covers.
rm -f "$OUT/orig_sizes.vh"
[ -f build/pnr/sizes.vh ] && cp build/pnr/sizes.vh "$OUT/orig_sizes.vh"

cat > $OUT/sizes.vh <<EOF
// One cell with no matched delay at all.  Everything else at its placeholder.
\`define $VICTIM_MACRO 0
EOF

if ! BD_SIZES=$OUT/sizes.vh ./flow.sh > $OUT/flow.log 2>&1; then
    echo "teeth: the under-delayed design would not build"
    tail -20 $OUT/flow.log
    exit 2
fi

python3 verify/tighten.py --list-audited > $OUT/after.txt 2>&1
if grep -q "^$VICTIM_MACRO " $OUT/after.txt; then
    echo "TEETH FAIL: after defining $VICTIM_MACRO 0, $VICTIM_PATH still has a"
    echo "            delay chain.  The BD_SIZES override never reached the"
    echo "            source, so nothing was sabotaged and the rest of this"
    echo "            gate would have been checking an unmodified design."
    grep "^$VICTIM_MACRO " $OUT/before.txt $OUT/after.txt
    exit 1
fi

if python3 verify/tighten.py > $OUT/tighten.log 2>&1; then
    echo "TEETH FAIL: the sizing pass PASSED a design with no matched delay on"
    echo "            $VICTIM_PATH.  It is not checking what it claims to check."
    sed -n '1,20p' $OUT/tighten.log
    exit 1
fi

if ! grep -q "$VICTIM_PATH.*VIOLATION" $OUT/tighten.log; then
    echo "TEETH FAIL: the sizing pass failed, but not on $VICTIM_PATH -- so it"
    echo "            objected to something other than the delay that was"
    echo "            removed, and this gate did not test what it thinks."
    grep VIOLATION $OUT/tighten.log | head -5
    exit 1
fi

grep -E "$VICTIM_PATH|VIOLATION" $OUT/tighten.log | head -3
echo "teeth.sh PASS -- the sizing gate catches a removed delay line"

# Leave the build directory holding the real design, not this one, so a later
# gate cannot accidentally read the sabotaged SDF.  Restore with the SAME
# sizes the census build used (one explicit, cheap re-route) rather than a
# bare ./flow.sh, which under the default-tighten path would re-run all of
# verify/resize.sh a second time just to clean up after this sabotage --
# correct, but a needless multi-route cost for a step whose only job is to
# put back what was already there.  No saved sizes means the census itself
# was an untightened (BD_NO_TIGHTEN=1) build, so restore the same way.
if [ -f "$OUT/orig_sizes.vh" ]; then
    BD_SIZES=$OUT/orig_sizes.vh ./flow.sh > $OUT/restore.log 2>&1 || true
else
    BD_NO_TIGHTEN=1 ./flow.sh > $OUT/restore.log 2>&1 || true
fi
