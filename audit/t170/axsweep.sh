#!/usr/bin/env bash
# axsweep.sh MODULE... : collectAxioms on every constant defined in a module whose name starts with Formal. (imports given modules)
set -euo pipefail
cd /root/agentJ/wt/formal/lean
export PATH=/root/audit-lean/lean-4.35.0-linux/bin:$PATH LEAN_NUM_THREADS=2
OUT=/root/agentJ/axsweep_tmp.lean
{ for m in "$@"; do echo "import $m"; done
cat <<'L'
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ok := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut n : Nat := 0
  let mut bad : Nat := 0
  let mut inRF : Nat := 0
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mn := env.header.moduleNames[idx.toNat]!
    unless (`Formal).isPrefixOf mn do continue
    n := n + 1
    if (`Formal.Rewrite.RingFuse).isPrefixOf mn then inRF := inRF + 1
    let axs ← liftCoreM (Lean.collectAxioms c)
    for a in axs do
      unless ok.contains a do
        bad := bad + 1
        logInfo s!"BAD {c} ({mn}) uses {a}"
  logInfo s!"AUDIT constants={n} ringfuse_constants={inRF} bad={bad}"
L
} > $OUT
nice -n 10 lake env lean $OUT 2>&1
