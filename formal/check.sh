#!/usr/bin/env bash
# Build every claimed file (all of formal/lean/Formal/**) and fail if any
# declaration in them depends on sorry, native_decide (Lean.ofReduceBool /
# ofReduceNat), or any axiom other than propext, Classical.choice, Quot.sound.
# Also fails on a textual `sorry`/`admit`/`axiom`/`native_decide` in a source
# file, as a second line of defence. Work in progress goes in formal/lean/Wip/.
#   formal/check.sh            # whole project
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
cd "$HERE/lean"
fail=0
echo "[check] textual scan"
if grep -rnE '(^|[^A-Za-z_.])(sorry|admit|native_decide)([^A-Za-z_]|$)|^[[:space:]]*(private |protected )?axiom[[:space:]]' \
     --include='*.lean' Formal Formal.lean | grep -vE '^\S+:[0-9]+:\s*--'; then
  echo "[check] FAIL: forbidden token in a claimed file (comments excepted)"; fail=1
fi
echo "[check] lake build"
FORMAL_SLOT_CWD="$HERE/lean" "$HERE/slot.sh" lake build 2>&1 | tee .lake/check-build.log | grep -E 'error|warning: declaration uses|Build completed|✖' | head -50
grep -q 'Build completed successfully' .lake/check-build.log || { echo "[check] FAIL: build"; fail=1; }
mods=$(find Formal -name '*.lean' | sed 's|\.lean$||; s|/|.|g' | sort)
mkdir -p .lake/audit
{ echo "import Formal"; for m in $mods; do echo "import $m"; done
  cat <<'LEAN'
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array String := #[]
  let mut n := 0
  for (c, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`Formal).isPrefixOf mod do continue
    if c.isInternal then continue
    n := n + 1
    let axs ← collectAxioms c
    for a in axs do
      unless ok.contains a do bad := bad.push s!"{c} uses {a}"
  IO.println s!"[audit] {n} declarations checked"
  for b in bad do IO.println s!"[audit] BAD: {b}"
  if bad.size > 0 then throwError "audit failed"
LEAN
} > .lake/audit/Audit.lean
echo "[check] axiom audit"
if [ $fail -eq 0 ]; then
  FORMAL_SLOT_CWD="$HERE/lean" "$HERE/slot.sh" lake env lean .lake/audit/Audit.lean || { echo "[check] FAIL: audit"; fail=1; }
fi
[ $fail -eq 0 ] && echo "[check] OK" || echo "[check] FAILED"
exit $fail
