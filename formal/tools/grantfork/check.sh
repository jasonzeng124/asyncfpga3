#!/usr/bin/env bash
# C-10i: H_GRANT_FORK on the routed bd_arbiter instances.
#   formal/tools/grantfork/check.sh          # extract (~40 s) + Lean (~20 s) + negative control
# Inputs (read-only): formal/tools/tcheck/build/tree_{2,3,4,d}/cells/build/hw/gcd_hw/,
# formal/tools/fasm2lean2/build/link_arb_s{1..4}*.  Outputs: build/ here, and the
# generated formal/lean/Formal/Timing/GrantForkInst.lean (checked for drift).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); LEAN=$(cd "$HERE/../../lean" && pwd)
mkdir -p "$HERE/build"
python3 -I "$HERE/extract.py" --lean "$HERE/build/GrantForkInst.lean"
cmp "$HERE/build/GrantForkInst.lean" "$LEAN/Formal/Timing/GrantForkInst.lean" \
  || { echo "DRIFT: committed GrantForkInst.lean differs from a fresh extraction"; exit 1; }
python3 -I "$HERE/summarize.py"
python3 -I "$HERE/ackcheck.py"
cd "$LEAN"; export PATH=$HOME/.elan/bin:$PATH LEAN_PATH=$PWD/.lake/build/lib/lean
mkdir -p .lake/build/lib/lean/Formal/Timing
../slot.sh lean -o .lake/build/lib/lean/Formal/Timing/GrantFork.olean Formal/Timing/GrantFork.lean
../slot.sh lean Formal/Timing/GrantForkInst.lean
python3 ../scan.py Formal/Timing/GrantFork.lean Formal/Timing/GrantForkInst.lean
# negative control: flip one passing verdict; the kernel must refuse it
sed 's/theorem gd_merge2_uarb1_c2_SMAX_T : okT gd_merge2_uarb1_c2_SMAX = true/theorem gd_merge2_uarb1_c2_SMAX_T : okT gd_merge2_uarb1_c2_SMAX = false/' \
  Formal/Timing/GrantForkInst.lean > "$HERE/build/NegInst.lean"
if ../slot.sh lean "$HERE/build/NegInst.lean" > "$HERE/build/neg.log" 2>&1; then
  echo "NEGATIVE CONTROL DID NOT FAIL"; exit 1; fi
grep -q "proved that the proposition" "$HERE/build/neg.log" && echo "negative control: refused (ok)"
echo "C-10i check PASS"
