#!/usr/bin/env bash
# Probe K2: compile what xaudit / xevents5 need WITHOUT lake build (forbidden here), each module
# through ../lean.sh (formal/slot.sh, lake's module setup, private olean dir $XAUDIT_OLEAN), in
# import order.  Neither executable imports Mathlib, so this works while Mathlib is still building.
#   XAUDIT_OLEAN=~/k2olean k2/mk_k2.sh                  -> oleans for `lean --run ...Events5Main.lean`
#   then XAUDIT_OUT=~/k2xa XAUDIT_OLEAN=~/k2olean ../build.sh   -> native $XAUDIT_OUT/xaudit
# Once the lake build has the lean_exe targets, `lake exe xaudit` / `lake exe xevents5` replace this.
set -euo pipefail
K2="$(cd "$(dirname "$0")" && pwd)"
LEAN="$(cd "$K2/../../../lean" && pwd)"
export XAUDIT_OLEAN=${XAUDIT_OLEAN:-$HOME/k2olean}
cd "$LEAN"
order=$(python3 -I - <<'PY'
import os
def imps(m):
    return [l.split()[1] for l in open(m.replace('.', '/') + '.lean') if l.startswith('import ')]
out, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for i in imps(m):
        if i.startswith('Formal.'): visit(i)
    out.append(m)
for r in ['Formal.Core.XAudit.Main', 'Formal.Core.XAudit.Events5Main']: visit(r)
print(' '.join(m.replace('.', '/') for m in out))
PY
)
for m in $order; do
  o="$XAUDIT_OLEAN/$m.olean"
  if [ -f "$o" ] && [ ! -L "$o" ] && [ "$o" -nt "$m.lean" ]; then continue; fi
  if [ "$m" = Formal/Core/XAudit/Main ] || [ "$m" = Formal/Core/XAudit/Events5Main ]; then continue; fi
  t0=$(date +%s)
  "$K2/../lean.sh" "$m.lean" > "$XAUDIT_OLEAN.$(echo $m | tr / _).log" 2>&1 || { echo "FAIL $m"; tail -5 "$XAUDIT_OLEAN.$(echo $m | tr / _).log"; exit 1; }
  echo "ok $m ($(( $(date +%s) - t0 )) s)"
done
