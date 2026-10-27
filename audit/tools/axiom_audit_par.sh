#!/usr/bin/env bash
# Resumable, parallel per-module axiom audit. Usage: axiom_audit_par.sh <lean project> <outdir> [jobs]
# Writes <outdir>/<Module>.res ("constants=N bad=B" or "NO RESULT") and <outdir>/<Module>.out; skips modules
# that already have a .res. Then prints a summary. Same check as axiom_audit_permod.sh.
set -uo pipefail
P=${1:?project}; OUT=${2:?outdir}; J=${3:-3}
mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
cd "$P"
one() {
  M=$1; OUT=$2
  [ -f "$OUT/$M.res" ] && return
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
  logInfo s!"MOD constants={n} bad={bad}"
L
  lake env lean $T > "$OUT/$M.out" 2>&1; rm -f $T
  r=$(grep -o "constants=[0-9]* bad=[0-9]*" "$OUT/$M.out" | tail -1)
  echo "${r:-NO RESULT}" > "$OUT/$M.res"
}
export -f one
find Formal -name '*.lean' | sort | sed 's#/#.#g; s#\.lean$##' | xargs -P "$J" -I{} bash -c 'one {} '"$OUT"
tot=0; bad=0; nores=0
for r in "$OUT"/*.res; do
  l=$(cat "$r")
  if [ "$l" = "NO RESULT" ]; then nores=$((nores+1)); echo "NO RESULT $(basename "$r" .res)"; continue; fi
  n=${l#constants=}; n=${n% bad=*}; b=${l#*bad=}; tot=$((tot+n)); bad=$((bad+b))
done
grep -h "BAD" "$OUT"/*.out 2>/dev/null | head -50
echo "AUDIT-PAR constants=$tot bad=$bad no_result=$nores modules=$(ls "$OUT"/*.res | wc -l)"
