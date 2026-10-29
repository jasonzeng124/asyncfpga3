#!/usr/bin/env bash
# Probe HDsub: compile listed modules (paths relative to formal/lean, in dependency order) into the
# private overlay /tmp/events9/olean (a full mirror of lake's build tree as symlinks, replaced by
# each module compiled here), until the lead's lake build has the XAudit oleans.
#   mk9.sh Formal/Core/XAudit/Design.lean ...      (or: mk9.sh --deps  = the Events8Main closure)
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/asyncfpga3/formal/lean
OL=${OL:-/tmp/events9/olean}
mkdir -p /tmp/events9/log $OL
[ -d $OL/Formal ] || cp -rs "$PWD/.lake/build/lib/lean/Formal" $OL/
if [ "${1:-}" = "--deps" ]; then
  set -- $(python3 -I - <<'PY'
import os
def imps(m): return [l.split()[1] for l in open(m.replace('.','/')+'.lean') if l.startswith('import ')]
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for i in imps(m):
        if i.startswith('Formal.'): visit(i)
    order.append(m)
visit('Formal.Core.XAudit.Events8Main')
print(' '.join(m.replace('.','/')+'.lean' for m in order
               if not os.path.exists('.lake/build/lib/lean/'+m.replace('.','/')+'.olean')))
PY
)
fi
for f in "$@"; do
  o=$OL/${f%.lean}.olean
  mkdir -p $(dirname $o); rm -f $o ${o%.olean}.ilean
  FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="$OL:$LEAN_PATH" exec lean -DautoImplicit=false -o "$1" "$2"' sh "$o" "$f" > /tmp/events9/log/mk_$(basename $f).log 2>&1
  rc=$?
  echo "$f rc=$rc errors=$(grep -c 'error' /tmp/events9/log/mk_$(basename $f).log)"
  [ $rc = 0 ] || { head -30 /tmp/events9/log/mk_$(basename $f).log; break; }
done
