#!/usr/bin/env bash
# Per-module variant of axiom_audit.sh (needed when two modules cannot be imported together,
# e.g. both define `main`). For each module M under Formal/, imports only M and audits the
# constants whose defining module is exactly M. Prints BAD lines and a total.
set -uo pipefail
P=${1:?project}; cd "$P"
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
TOT=0; BAD=0; FAILMOD=0
for f in $(find Formal -name '*.lean' | sort); do
  M=$(echo $f | sed 's#/#.#g; s#\.lean$##')
  T=$(mktemp --suffix=.lean)
  cat > $T <<L
import Lean
import $M
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ok := #[\`\`propext, \`\`Classical.choice, \`\`Quot.sound]
  let mut n : Nat := 0
  let mut bad : Nat := 0
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    unless env.header.moduleNames[idx.toNat]! == \`$M do continue
    n := n + 1
    let axs ← liftCoreM (Lean.collectAxioms c)
    for a in axs do
      unless ok.contains a do
        bad := bad + 1
        logInfo s!"BAD {c} uses {a}"
  logInfo s!"MOD $M constants={n} bad={bad}"
L
  out=$(lake env lean $T 2>&1); rm -f $T
  echo "$out" | grep -E "BAD|error" | sed "s#^#[$M] #"
  line=$(echo "$out" | grep -o "constants=[0-9]* bad=[0-9]*")
  if [ -z "$line" ]; then FAILMOD=$((FAILMOD+1)); echo "[$M] NO RESULT"; continue; fi
  n=${line#constants=}; n=${n% bad=*}; b=${line#*bad=}
  TOT=$((TOT+n)); BAD=$((BAD+b))
done
echo "AUDIT-PERMOD constants=$TOT bad=$BAD modules_failed=$FAILMOD"
