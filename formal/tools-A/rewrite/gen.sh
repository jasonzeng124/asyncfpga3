#!/usr/bin/env bash
# Shard A: regenerate the Lean imports of research's rewritten handshake MLIRs (PROGRAM.md, "FIRST", item 5).
# Inputs are read from origin/claude/research (read-only); outputs go to formal/lean/Formal/Rewrite/.
#   formal/tools-A/rewrite/gen.sh      then   cd formal && ./check.sh Formal/Rewrite/<file>.lean ...
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; ROOT="$(cd "$HERE/../../.." && pwd)"; cd "$ROOT"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
O=formal/lean/Formal/Rewrite; mkdir -p $O
for f in xorshift_predec collatz_preeq2 collatz64_preeq2; do
  git show origin/claude/research:research/data/fifteen/$f.mlir > $T/$f.mlir; md5sum $T/$f.mlir; done
for k in xorshift collatz collatz64; do
  git show origin/claude/research:cloud/fixtures/frontend/$k/comp/handshake_transformed.mlir > $T/${k}_orig.mlir; done
# the committed rewrites are the scripts' outputs on the frontend fixtures
git show origin/claude/research:research/tools/fifteen/pre_dec.py > $T/pre_dec.py
git show origin/claude/research:research/tools/fifteen/pre_eq2.py > $T/pre_eq2.py
python3 -I $T/pre_dec.py $T/xorshift_orig.mlir $T/x.mlir && cmp $T/x.mlir $T/xorshift_predec.mlir
python3 -I $T/pre_eq2.py $T/collatz_orig.mlir $T/c.mlir && cmp $T/c.mlir $T/collatz_preeq2.mlir
python3 -I $T/pre_eq2.py $T/collatz64_orig.mlir $T/c64.mlir && cmp $T/c64.mlir $T/collatz64_preeq2.mlir
I=formal/tools/dfimport/mlir2lean.py; A=formal/tools/autoproof/autoproof.py
for spec in "xorshift_predec XorshiftPredec xorshift" "collatz_preeq2 CollatzPreeq2 collatz" "collatz64_preeq2 Collatz64Preeq2 collatz64" \
            "collatz64_orig Collatz64Orig collatz64"; do
  set -- $spec
  python3 $I $T/$1.mlir -o $O/$2Hw.lean --segments $O/$2HwSeg.lean --ns Formal.Rewrite.$2Hw \
    --graph-module Formal.Rewrite.$2Hw --label $1 --short $3
  sed -i "s|^Source: \`[^\`]*/$1.mlir\`|Source: \`research/data/fifteen/$1.mlir\` (origin/claude/research)|" $O/$2Hw.lean
done
sed -i "s|^Source: \`research/data/fifteen/collatz64_orig.mlir\` (origin/claude/research)|Source: \`cloud/fixtures/frontend/collatz64/comp/handshake_transformed.mlir\` (origin/claude/research)|" $O/Collatz64OrigHw.lean
# collatz (32-bit): autoproof against kernels/collatz/collatz.c; its one rewrite obligation closed by Eq2
python3 $A $T/collatz_preeq2.mlir kernels/collatz/collatz.c collatz --name CollatzPreeq2 \
  --graph-ns Formal.Rewrite.CollatzPreeq2Hw --seg-module Formal.Rewrite.CollatzPreeq2HwSeg \
  --out $O/AutoCollatzPreeq2.lean --vecs "6 7 27"
python3 $HERE/patch_eq2.py $O/AutoCollatzPreeq2.lean 32
python3 -c 'import re,sys; p=sys.argv[1]; s=open(p).read(); open(p,"w").write(re.sub(r"export of `[^`]*/collatz_preeq2.mlir`", "export of `research/data/fifteen/collatz_preeq2.mlir`", s))' $O/AutoCollatzPreeq2.lean
sed -i 's/^namespace Formal.Net.AutoCollatzPreeq2/namespace Formal.Rewrite.AutoCollatzPreeq2/; s/^end Formal.Net.AutoCollatzPreeq2/end Formal.Rewrite.AutoCollatzPreeq2/' $O/AutoCollatzPreeq2.lean
