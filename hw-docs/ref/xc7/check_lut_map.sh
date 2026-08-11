#!/usr/bin/env bash
# SAT equivalence check for boards/xc7/sb_lut4_map.v (SB_LUT4 -> LUT4).
#
# Silent LUT-truth-table corruption (wrong init-bit permutation) is the
# failure mode that costs weeks on hardware, so this is mandatory and cheap:
# for a battery of init values, build gold_<k> (SB_LUT4, flattened into the
# iCE40 simulation model = ground truth) and gate_<k> (the SAME instance run
# through the real map file, flattened into the Xilinx simulation model),
# then miter + `sat -verify` proves them equal over all 16 input patterns.
#
# The init battery deliberately includes the four single-variable functions
# (0xFF00=I3, 0xF0F0=I2, 0xCCCC=I1, 0xAAAA=I0 -- these are also the library's
# IA/IB/IC/ID encodings from rtl/common/lut.sv), which catch any pin
# permutation or init bit-reversal, plus asymmetric random tables that catch
# everything else.
#
#   check_lut_map.sh [workdir]      (default workdir: mktemp)
set -euo pipefail

BOARD_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
YOSYS="${YOSYS:-$HOME/dev2/lib/fpgatoolchain/yosys/build/yosys}"
WORK="${1:-$(mktemp -d /tmp/lutcheck.XXXXXX)}"
mkdir -p "$WORK"

INITS="ff00 f0f0 cccc aaaa 8000 0001 6996 ca53 1ee4 7fe8 35c9 b426"

# gold_<k>/gate_<k> start as identical SB_LUT4 wrappers; only gate_* is
# techmapped, so any mapping error shows up as a miter mismatch.
PAIRS="$WORK/pairs.v"
: > "$PAIRS"
for v in $INITS; do
  for side in gold gate; do
    cat >> "$PAIRS" <<EOF
module ${side}_${v} (input i0, i1, i2, i3, output o);
  SB_LUT4 #(.LUT_INIT(16'h${v})) l (.O(o), .I0(i0), .I1(i1), .I2(i2), .I3(i3));
endmodule
EOF
  done
done

{
  echo "read_verilog $PAIRS"
  # Map ONLY the gate_* modules with the file under test (SB_LUT4 cells are
  # still unresolved here, exactly as in the real flow).
  echo "techmap -map $BOARD_DIR/sb_lut4_map.v gate_*"
  echo "select -assert-none gate_*/t:SB_LUT4"
  # Now bring in both vendors' behavioral models and flatten each side into
  # its own family's ground truth.
  echo "read_verilog +/ice40/cells_sim.v"
  echo "read_verilog +/xilinx/cells_sim.v"
  # LOAD-BEARING: without this hierarchy pass, flatten binds the SB_LUT4/
  # LUT4 instances against the not-yet-processed library modules and DROPS
  # the LUT_INIT/INIT parameter -- both sides collapse to INIT=0 and every
  # miter passes vacuously (measured: a deliberately pin-swapped map file
  # sailed through). hierarchy elaborates the modules so parameters bind.
  echo "hierarchy"
  for v in $INITS; do
    echo "flatten gold_${v} gate_${v}"
    echo "miter -equiv -flatten gold_${v} gate_${v} miter_${v}"
    echo "sat -verify -prove trigger 0 -show-inputs -show-outputs miter_${v}"
  done
  # Anti-vacuousness anchors: independently of the miters, prove BOTH sides
  # of the four single-variable pairs compute the actual function of the
  # right input (o == i_k). If a future yosys change ever drops parameters
  # again, both the anchors and nothing else would still be INIT=0 constants
  # and these proofs fail.
  for side in gold gate; do
    echo "sat -verify -prove o 1 -set i3 1 ${side}_ff00"
    echo "sat -verify -prove o 0 -set i3 0 ${side}_ff00"
    echo "sat -verify -prove o 1 -set i2 1 ${side}_f0f0"
    echo "sat -verify -prove o 0 -set i2 0 ${side}_f0f0"
    echo "sat -verify -prove o 1 -set i1 1 ${side}_cccc"
    echo "sat -verify -prove o 0 -set i1 0 ${side}_cccc"
    echo "sat -verify -prove o 1 -set i0 1 ${side}_aaaa"
    echo "sat -verify -prove o 0 -set i0 0 ${side}_aaaa"
  done
} > "$WORK/check.ys"

# Expected proof count: one miter per init value + 8 anchor proofs per side.
EXPECT=$(( $(echo $INITS | wc -w) + 16 ))
if "$YOSYS" -q -l "$WORK/check.log" -s "$WORK/check.ys"; then
  n=$(grep -c "SAT proof finished - no model found: SUCCESS" "$WORK/check.log" || true)
  if [ "$n" -ne "$EXPECT" ]; then
    echo "LUT map equivalence check FAILED: $n SAT proofs found, expected $EXPECT -- see $WORK/check.log" >&2
    exit 1
  fi
  echo "LUT map equivalence check PASS ($(echo $INITS | wc -w) init miters + 16 anchor proofs SAT-proven; log: $WORK/check.log)"
else
  echo "LUT map equivalence check FAILED -- see $WORK/check.log" >&2
  exit 1
fi
