#!/usr/bin/env bash
# Regenerate the claimed generated proofs of probe C-vk2 (formal/notes/C-vk2-autoproof.md).
# Python only; check them afterwards with
#   cd formal && ./check.sh Formal/Net/AutoLib.lean Formal/Net/AutoIpow.lean Formal/Net/AutoCollatz.lean \
#     Formal/Net/AutoXorshift.lean Formal/Net/AutoGcd.lean Formal/Net/AutoGcdSubi0Hw.lean \
#     Formal/Net/AutoGcdSubi0HwSeg.lean Formal/Net/AutoGcdSubi0.lean Formal/Net/AutoIsprimeHw.lean \
#     Formal/Net/AutoIsprimeHwSeg.lean Formal/Net/AutoIsprime.lean
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; ROOT="$(cd "$HERE/../../.." && pwd)"; cd "$ROOT"
A=formal/tools/autoproof/autoproof.py; F=cloud/fixtures/frontend; N=formal/lean/Formal/Net
python3 $A $F/ipow/comp/handshake_transformed.mlir kernels/ipow/ipow.c ipow --name Ipow \
  --graph-ns Formal.Net.IpowHw --seg-module Formal.Net.IpowHwSeg --out $N/AutoIpow.lean --vecs "3,7 2,10 -3,5"
python3 $A $F/collatz/comp/handshake_transformed.mlir kernels/collatz/collatz.c collatz --name Collatz \
  --graph-ns Formal.Net.CollatzHw --seg-module Formal.Net.CollatzHwSeg --out $N/AutoCollatz.lean --vecs "6 7 27"
python3 $A $F/xorshift/comp/handshake_transformed.mlir kernels/xorshift/xorshift.c xorshift --name Xorshift \
  --graph-ns Formal.Net.XorshiftHw --seg-module Formal.Net.XorshiftHwSeg --out $N/AutoXorshift.lean \
  --vecs "-1831433054,4 1,1"
python3 $A $F/gcd/comp/handshake_transformed.mlir formal/tools/autoproof/ref/gcd_binary.c gcd --name Gcd \
  --graph-ns Formal.Net.GcdHw.Gcd --seg-module Formal.Net.GcdHwSeg --out $N/AutoGcd.lean \
  --vecs "12,18 35,14 48,180 0,7 9,0"
# the equivalent mutant of C-vk (gcd, subi0's operands swapped): its own graph and segments
python3 formal/tools/verify/mutate.py $F/gcd/comp/handshake_transformed.mlir formal/tools/autoproof/test/gcd_subi0.mlir \
  --swap subi0
python3 formal/tools/dfimport/mlir2lean.py formal/tools/autoproof/test/gcd_subi0.mlir -o $N/AutoGcdSubi0Hw.lean \
  --segments $N/AutoGcdSubi0HwSeg.lean --ns Formal.Net.AutoGcdSubi0Hw --graph-module Formal.Net.AutoGcdSubi0Hw \
  --label gcd_hw_subi0_swapped --short gcd
python3 $A formal/tools/autoproof/test/gcd_subi0.mlir formal/tools/autoproof/ref/gcd_binary.c gcd --name GcdSubi0 \
  --graph-ns Formal.Net.AutoGcdSubi0Hw --seg-module Formal.Net.AutoGcdSubi0HwSeg --out $N/AutoGcdSubi0.lean \
  --vecs "12,18 35,14 48,180 0,7 9,0"
# isprime: a kernel with no hand proof (nested loops, early returns); graph exported here
python3 formal/tools/dfimport/mlir2lean.py $F/isprime/comp/handshake_transformed.mlir -o $N/AutoIsprimeHw.lean \
  --segments $N/AutoIsprimeHwSeg.lean --ns Formal.Net.AutoIsprimeHw --graph-module Formal.Net.AutoIsprimeHw \
  --label isprime --short isprime
python3 $A $F/isprime/comp/handshake_transformed.mlir kernels/isprime/isprime.c isprime --name Isprime \
  --graph-ns Formal.Net.AutoIsprimeHw --seg-module Formal.Net.AutoIsprimeHwSeg --out $N/AutoIsprime.lean \
  --vecs "97 91 2 1 7919"
