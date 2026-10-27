#!/usr/bin/env bash
# Build every claimed file (all of formal/lean/Formal/**) and fail if any
# declaration in them depends on sorry, native_decide (Lean.ofReduceBool /
# ofReduceNat), or any axiom other than propext, Classical.choice, Quot.sound.
# Also fails on a textual `sorry`/`admit`/`axiom`/`native_decide` in a source
# file, as a second line of defence. Work in progress goes in formal/lean/Wip/.
#   formal/check.sh            # whole project
#   formal/check.sh --committed   # only git-tracked files under Formal/ (lake build + audit)
#   formal/check.sh FILE...    # only these files (paths relative to formal/lean),
#                              # checked with `lake env lean` (oleans go to .lake/checkfile,
#                              # never .lake/build, so lake's traces stay valid), then audited
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
cd "$HERE/lean"
fail=0
COMMITTED=0
if [ "${1:-}" = "--committed" ]; then COMMITTED=1; shift; fi
FILES=("$@")
echo "[check] textual scan"
if [ ${#FILES[@]} -gt 0 ]; then SCAN=("${FILES[@]}")
elif [ $COMMITTED -eq 1 ]; then mapfile -t SCAN < <(git ls-files Formal Formal.lean | grep '\.lean$')
else mapfile -t SCAN < <(find Formal Formal.lean -name '*.lean'); fi
python3 "$HERE/scan.py" "${SCAN[@]}" || { echo "[check] FAIL: forbidden token in a claimed file (comments excepted)"; fail=1; }
if [ ${#FILES[@]} -eq 0 ]; then
echo "[check] lake build"
TARGETS=(); [ $COMMITTED -eq 1 ] && TARGETS=($(printf '%s\n' "${SCAN[@]}" | grep '^Formal/' | sed 's|\.lean$||; s|/|.|g'))
FORMAL_SLOT_CWD="$HERE/lean" "$HERE/slot.sh" lake build "${TARGETS[@]}" 2>&1 | tee .lake/check-build.log | grep -E 'error|warning: declaration uses|Build completed|✖' | head -50
grep -q 'Build completed successfully' .lake/check-build.log || { echo "[check] FAIL: build"; fail=1; }
mods=$(printf '%s\n' "${SCAN[@]}" | grep '^Formal/' | sed 's|\.lean$||; s|/|.|g' | sort)
else
  for f in "${FILES[@]}"; do
    echo "[check] lean $f"; mkdir -p ".lake/checkfile/$(dirname "$f")"
    FORMAL_SLOT_CWD="$HERE/lean" "$HERE/slot.sh" lake env sh -c 'LEAN_PATH="$PWD/.lake/checkfile:$LEAN_PATH" exec lean -o ".lake/checkfile/${1%.lean}.olean" "$1"' sh "$f" > ".lake/check-file.log" 2>&1 || { grep -E 'error' .lake/check-file.log | head -20; echo "[check] FAIL: $f"; fail=1; }
  done
  mods=$(printf '%s\n' "${FILES[@]}" | sed 's|\.lean$||; s|/|.|g')
fi
mkdir -p .lake/audit
{ echo "import Lean"; [ ${#FILES[@]} -eq 0 ] && [ $COMMITTED -eq 0 ] && echo "import Formal"; for m in $mods; do echo "import $m"; done
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
  FORMAL_SLOT_CWD="$HERE/lean" "$HERE/slot.sh" lake env sh -c 'LEAN_PATH="$PWD/.lake/checkfile:$LEAN_PATH" exec lean .lake/audit/Audit.lean' || { echo "[check] FAIL: audit"; fail=1; }
fi
[ $fail -eq 0 ] && echo "[check] OK" || echo "[check] FAILED"
exit $fail
