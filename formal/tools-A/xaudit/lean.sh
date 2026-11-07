#!/usr/bin/env bash
# Check (and emit an olean for) one XAudit module, with a private olean dir
# for the XAudit modules (no lake build). Usage (from formal/lean):
#   ../tools-A/xaudit/lean.sh Formal/Core/XAudit/Design.lean [extra lean args]
set -euo pipefail
OL="${XAUDIT_OLEAN:-/tmp/xaudit/olean}"
f=$1; shift
mod=${f%.lean}
mkdir -p "$OL/$(dirname "$mod")"
# Lean resolves `Formal.*` in the first LEAN_PATH entry that has `Formal/`:
# mirror the lake build tree there as symlinks (read-only use).
[ -e "$OL/Formal/Core/XSim.olean" ] || cp -rsn "$PWD/.lake/build/lib/lean/Formal" "$OL/"
export PATH=$HOME/.elan/bin:$PATH
# the same module setup lake uses (package `formal`, so symbol names match lake's)
setup="$OL/$mod.setup.json"
# never write through a symlink into lake's build tree
[ -L "$OL/$mod.olean" ] && rm -f "$OL/$mod.olean"
python3 -I - "$mod" "$OL" "$PWD" > "$setup" <<'PY'
import json, re, sys, os
mod, ol, root = sys.argv[1], sys.argv[2], sys.argv[3]
def imports(m):
    src = os.path.join(root, m + ".lean")
    return [l.split()[1] for l in open(src) if l.startswith("import ")]
seen, todo = [], [mod]
while todo:
    m = todo.pop()
    for i in imports(m):
        if i.startswith("Formal.") and i not in seen:
            seen.append(i); todo.append(i.replace(".", "/"))
arts = {}
for i in seen:
    p = i.replace(".", "/") + ".olean"
    mine = os.path.join(ol, p)
    lake = os.path.join(root, ".lake/build/lib/lean", p)
    arts[i] = [[mine if not os.path.islink(mine) and os.path.exists(mine) else lake]]
print(json.dumps({"plugins": [], "package": "formal", "options": {"autoImplicit": False},
                  "name": mod.replace("/", "."), "isModule": False, "importArts": arts, "dynlibs": []}))
PY
exec "$(dirname "$0")/../../slot.sh" lake env bash -c "LEAN_PATH=$OL:\$LEAN_PATH lean -o $OL/$mod.olean --setup $setup $f $*"
