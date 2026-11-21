#!/usr/bin/env bash
# KapRes2 (2026-10-29): compile the COMMITTED xevents8 module chain (Mathlib-free, 32 modules)
# into a private olean overlay $OL, in import order, through slot.sh, with the lakefile's
# leanOptions (-DautoImplicit=false).  Never touches .lake/build.  A module whose olean already
# exists in $OL is skipped (delete $OL to rebuild).
export PATH=$HOME/.elan/bin:$PATH
OL=${OL:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/KapRes2/olean}
cd /home/user/asyncfpga3/formal/lean
mkdir -p $OL $OL.log
MODS=$(python3 - "$@" <<'PY'
import os, re, sys
roots = sys.argv[1:] or ["Formal.Core.XAudit.Events8Main"]
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    p = m.replace(".", "/") + ".lean"
    if not os.path.exists(p): return
    for l in open(p):
        mm = re.match(r"\s*import\s+(\S+)", l)
        if mm: visit(mm.group(1))
    order.append(p)
for r in roots: visit(r)
print(" ".join(order))
PY
)
for f in $MODS; do
  o=$OL/${f%.lean}.olean
  [ -e "$o" ] && continue
  mkdir -p $(dirname $o)
  FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c "LEAN_PATH=\"$OL:\$LEAN_PATH\" exec lean -DautoImplicit=false -o \"\$1\" \"\$2\"" sh "$o" "$f" > $OL.log/$(basename $f).log 2>&1
  rc=$?; ne=$(grep -cE '(^|: )error' $OL.log/$(basename $f).log)
  echo "$f rc=$rc errors=$ne"
  if [ $rc -ne 0 ] || [ $ne -ne 0 ]; then rm -f "$o"; exit 1; fi
done
echo "overlay $OL complete"
