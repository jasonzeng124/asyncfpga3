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
  # per-run directory: concurrent runs (probes use check.sh too) must not share it,
  # and stale oleans there would shadow lake's (it is first on LEAN_PATH)
  CHK=".lake/checkfile.$$"; rm -rf "$CHK"; trap 'rm -rf "$CHK" "$CHK.log"' EXIT; export CHK
  # Lean takes Formal.* from the first LEAN_PATH entry that has a Formal/ dir, so CHK
  # must be a full overlay: symlinks to lake's oleans, replaced by each file checked.
  mkdir -p "$CHK"; [ -d .lake/build/lib/lean/Formal ] && cp -rs "$PWD/.lake/build/lib/lean/Formal" "$CHK/"
  for f in "${FILES[@]}"; do
    echo "[check] lean $f"; mkdir -p "$CHK/$(dirname "$f")"; rm -f "$CHK/${f%.lean}.olean" "$CHK/${f%.lean}.ilean"
    FORMAL_SLOT_CWD="$HERE/lean" "$HERE/slot.sh" lake env sh -c 'LEAN_PATH="$PWD/$CHK:$LEAN_PATH" exec lean -o "$CHK/${1%.lean}.olean" "$1"' sh "$f" > "$CHK.log" 2>&1 || { grep -E 'error' "$CHK.log" | head -20; echo "[check] FAIL: $f"; fail=1; }
  done
  mods=$(printf '%s\n' "${FILES[@]}" | sed 's|\.lean$||; s|/|.|g')
fi
# Modules that define `main` (executables) clash when imported together, so each is
# audited in its own run; all other modules are audited together.
LIBMODS=(); EXEMODS=()
for m in $mods; do
  if grep -qE '^def main' "$(echo "$m" | tr . /).lean" 2>/dev/null; then EXEMODS+=("$m"); else LIBMODS+=("$m"); fi
done
mkdir -p .lake/audit
audit_run() {  # $1 = header flag (root|none), rest = modules
  local root=$1; shift
  local AUD=".lake/audit/Audit.$$.$RANDOM.lean"
  { echo "import Lean"; [ "$root" = root ] && echo "import Formal"; for m in "$@"; do echo "import $m"; done
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
  } > "$AUD"
  FORMAL_SLOT_CWD="$HERE/lean" "$HERE/slot.sh" lake env sh -c 'LEAN_PATH="$PWD/${CHK:-.lake/none}:$LEAN_PATH" exec lean "$0"' "$AUD"
  local rc=$?; rm -f "$AUD"; return $rc
}
echo "[check] axiom audit"
if [ $fail -eq 0 ]; then
  ROOT=none; [ ${#FILES[@]} -eq 0 ] && [ $COMMITTED -eq 0 ] && ROOT=root
  audit_run $ROOT "${LIBMODS[@]}" || { echo "[check] FAIL: audit"; fail=1; }
  for m in "${EXEMODS[@]}"; do
    echo "[check] audit (executable) $m"
    audit_run none "$m" || { echo "[check] FAIL: audit $m"; fail=1; }
  done
fi
[ $fail -eq 0 ] && echo "[check] OK" || echo "[check] FAILED"
exit $fail
