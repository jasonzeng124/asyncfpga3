#!/usr/bin/env bash
# Probe K3 (k2/mk_k2.sh with the xevents8 roots): compile what xaudit / xevents5 need WITHOUT lake build (forbidden here), each module
# through ../lean.sh (formal/slot.sh, lake's module setup, private olean dir $XAUDIT_OLEAN), in
# import order.  Neither executable imports Mathlib, so this works while Mathlib is still building.
#   XAUDIT_OLEAN=~/k3olean k3/mk_k3.sh                  -> oleans for `lean --run ...Events5Main.lean`
#   then XAUDIT_OUT=~/k3xa XAUDIT_OLEAN=~/k3olean ../build.sh   -> native $XAUDIT_OUT/xaudit
# Once the lake build has the lean_exe targets, `lake exe xaudit` / `lake exe xevents5` replace this.
set -euo pipefail
K3="$(cd "$(dirname "$0")" && pwd)"
LEAN="$(cd "$K3/../../../lean" && pwd)"
export XAUDIT_OLEAN=${XAUDIT_OLEAN:-$HOME/k3olean}
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
for r in ['Formal.Core.XAudit.Main', 'Formal.Core.XAudit.Events5Main', 'Formal.Core.XAudit.Events8Main']: visit(r)
print(' '.join(m.replace('.', '/') for m in out))
PY
)
for m in $order; do
  o="$XAUDIT_OLEAN/$m.olean"
  if [ -f "$o" ] && [ ! -L "$o" ] && [ "$o" -nt "$m.lean" ]; then continue; fi
  if [ "$m" = Formal/Core/XAudit/Main ] || [ "$m" = Formal/Core/XAudit/Events5Main ] || [ "$m" = Formal/Core/XAudit/Events8Main ]; then continue; fi
  t0=$(date +%s)
  "$K3/../lean.sh" "$m.lean" > "$XAUDIT_OLEAN.$(echo $m | tr / _).log" 2>&1 || { echo "FAIL $m"; tail -5 "$XAUDIT_OLEAN.$(echo $m | tr / _).log"; exit 1; }
  echo "ok $m ($(( $(date +%s) - t0 )) s)"
done
# Native xaudit: ../build.sh (C for its 10 modules via lean.sh -c, linked with leanc) does not
# list Formal/Core/XAudit/Parse, which Main imports now, so its link fails with
# "undefined symbol: initialize_formal_Formal_Core_XAudit_Parse".  NATIVE=1 runs build.sh, then
# emits Parse's C the same way and relinks.  -> $XAUDIT_OUT/xaudit
if [ "${NATIVE:-0}" = 1 ]; then
  export XAUDIT_OUT=${XAUDIT_OUT:-$HOME/k3xa}
  "$K3/../build.sh" || true
  "$K3/../lean.sh" Formal/Core/XAudit/Parse.lean -c "$XAUDIT_OUT/c/Formal_Core_XAudit_Parse.c"
  LEANC="$(dirname "$(readlink -f "$(command -v lean)")")/leanc"
  [ -x "$LEANC" ] || LEANC="$(elan which lean | xargs dirname)/leanc"
  "$LEANC" -O2 -o "$XAUDIT_OUT/xaudit" "$XAUDIT_OUT"/c/*.c
  echo "[k2] built $XAUDIT_OUT/xaudit"
fi
