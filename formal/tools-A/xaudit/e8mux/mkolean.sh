#!/usr/bin/env bash
# E8Mux: compile Formal.Core.XAudit.Events8Main's import closure (the modules lake's .lake/build
# does not have yet) into a private olean overlay $OL, in dependency order, each lean through
# formal/slot.sh (as events8/mk8.sh).  Nothing is claimed from these oleans; they only run xevents8.
set -u
OL=${OL:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/e8mux/olean}
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/asyncfpga3/formal/lean
mkdir -p $OL/log
# Lean takes Formal.* from the FIRST LEAN_PATH entry that has a Formal/ dir: make $OL a full overlay
# (symlinks to lake's oleans, as check.sh does)
[ -d .lake/build/lib/lean/Formal ] && cp -rsn "$PWD/.lake/build/lib/lean/Formal" "$OL/" 2>/dev/null
order=$(python3 - <<'PY'
import re, os
out, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    p = m.replace('.', '/') + '.lean'
    if not os.path.exists(p): return
    for l in open(p):
        mm = re.match(r'import\s+(\S+)', l)
        if mm: visit(mm.group(1))
    out.append(p)
visit("Formal.Core.XAudit.Events8Main")
print(" ".join(out))
PY
)
for f in $order; do
  [ -L $OL/${f%.lean}.olean ] && continue      # lake has it
  o=$OL/${f%.lean}.olean
  [ -e $o ] && [ $o -nt $f ] && continue
  mkdir -p $(dirname $o)
  FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="$0:$LEAN_PATH" exec lean -DautoImplicit=false -o "$1" "$2"' "$OL" "$o" "$f" > $OL/log/$(basename $f).log 2>&1
  rc=$?; echo "$f rc=$rc errors=$(grep -c 'error' $OL/log/$(basename $f).log)"
  [ $rc -eq 0 ] || exit 1
done
echo "mkolean done"
