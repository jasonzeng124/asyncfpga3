#!/bin/bash
# Audit T5: build ToyRepairedInline.lean = the 6f094d32 Spec.lean text, verbatim, followed by ToyRepaired.lean's body
# (used while no 6f094d32 build exists; the import version ToyRepaired.lean is the one of record once it does).
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd)
SPEC=$(mktemp)
git -C /root/wt-f14 show 6f094d32:formal/lean/Formal/Target/Spec.lean > "$SPEC"
head -3 "$SPEC" | grep -q '^import Mathlib.Data.Nat.GCD.Basic' || { echo "unexpected Spec header"; exit 1; }
{ head -3 "$SPEC"; echo "import Mathlib.Tactic.Ring"; echo "import Mathlib.Tactic.NormNum";
  tail -n +4 "$SPEC"; echo; echo "-- ===== end of verbatim Spec.lean (6f094d32), start of audit T5 toy ====="; tail -n +4 "$D/ToyRepaired.lean"; } > "$D/ToyRepairedInline.lean"
# verify: lines 6..(5+n-3) of the inline file are exactly Spec lines 4..n
n=$(wc -l < "$SPEC")
if cmp -s <(sed -n "6,$((n+2))p" "$D/ToyRepairedInline.lean") <(tail -n +4 "$SPEC"); then echo "inlined Spec text identical to git show 6f094d32 (md5 $(md5sum < "$SPEC" | cut -c1-8))"; else echo "MISMATCH"; exit 1; fi
rm -f "$SPEC"
