#!/usr/bin/env bash
# Auditor's own axiom audit. Usage: axiom_audit.sh <lean project dir> [extra .lean file to import as module-free check]
# Imports every module under Formal/ (from the file tree, not their Formal.lean), then runs
# Lean.collectAxioms on EVERY constant whose defining module starts with `Formal.`; prints any
# axiom outside {propext, Classical.choice, Quot.sound}, plus counts.
set -euo pipefail
P=${1:?project}; cd "$P"
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
OUT=$(mktemp --suffix=.lean)
{ find Formal -name '*.lean' | sort | sed 's#/#.#g; s#\.lean$##; s#^#import #'
cat <<'L'
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ok := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut n := 0; let mut bad := 0
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mn := env.header.moduleNames[idx.toNat]!
    unless (`Formal).isPrefixOf mn do continue
    n := n + 1
    let axs ← liftCoreM (Lean.collectAxioms c)
    for a in axs do
      unless ok.contains a do
        bad := bad + 1
        logInfo m!"BAD {c} ({mn}) uses {a}"
  logInfo m!"AUDIT constants={n} bad={bad}"
L
} > $OUT
lake env lean $OUT 2>&1
