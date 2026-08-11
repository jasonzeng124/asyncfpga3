#!/usr/bin/env bash
# Does the sizing gate have teeth?
#
# A gate that has never failed is not evidence, it is decoration.  This builds
# the soak design a second time with bd_merge's matched delay removed entirely
# -- DELAY(0), which bd_delay renders as a bare wire, so there is not even a
# chain left in the netlist to find -- routes it, and requires
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
# sed and stopped working the moment the parameter was written differently --
# a check that silently turns into a no-op is worse than no check.
set -u
cd "$(dirname "$0")/.."

OUT=build/teeth
mkdir -p $OUT

cat > $OUT/sizes.vh <<'EOF'
// The merge with no matched delay at all.  Everything else at its placeholder.
`define BD_SZ_UMERGE 0
EOF

if ! BD_SIZES=$OUT/sizes.vh ./flow.sh > $OUT/flow.log 2>&1; then
    echo "teeth: the under-delayed design would not build"
    tail -20 $OUT/flow.log
    exit 2
fi

if python3 verify/tighten.py build/pnr/soak.sdf > $OUT/tighten.log 2>&1; then
    echo "TEETH FAIL: the sizing pass PASSED a design with no matched delay on"
    echo "            the merge.  It is not checking what it claims to check."
    sed -n '1,20p' $OUT/tighten.log
    exit 1
fi

grep -E "umerge|VIOLATION" $OUT/tighten.log | head -3
echo "teeth.sh PASS -- the sizing gate catches a removed delay line"

# Leave the build directory holding the real design, not this one, so a later
# gate cannot accidentally read the sabotaged SDF.
./flow.sh > $OUT/restore.log 2>&1 || true
