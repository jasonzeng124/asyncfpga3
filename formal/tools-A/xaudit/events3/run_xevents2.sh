#!/usr/bin/env bash
# Build Parse/Events2*/Events2Main into a private olean dir (no lake build) and run
# xevents2 (interpreter) on the designs; results go next to this script.
# Once the lead adds the [[lean_exe]] stanza (name "xevents2", root
# "Formal.Core.XAudit.Events2Main"), `lake exe xevents2 ARGS` replaces this.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
L="$(cd "$HERE/../../../lean" && pwd)"
export XAUDIT_OLEAN="${EVENTS3_OLEAN:-/tmp/xevents2/olean}"
export PATH=$HOME/.elan/bin:$PATH
cd "$L"
for f in Parse Events2 Events2Time Events2Design Events2Main; do
  ../tools-A/xaudit/lean.sh Formal/Core/XAudit/$f.lean 2>&1 | grep -E "error" || true
done
D=../tools-A/xaudit/designs
J=../tools/import/json
xe() { out=$1; shift; ../slot.sh lake env bash -c "LEAN_PATH=$XAUDIT_OLEAN:\$LEAN_PATH lean --run Formal/Core/XAudit/Events2Main.lean $*" > "$HERE/$out.txt" 2>&1 && rc=0 || rc=$?; echo "$out: exit $rc: $(grep VERDICT "$HERE/$out.txt" | cut -c1-60)"; }
xe pipe3_slow_corner_env10_500 $D/pipe3.json --bands $D/slow_corner.bands.json --env 10:500
xe pipe3_slow_corner_env10_1e10 $D/pipe3.json --bands $D/slow_corner.bands.json --env 10:10000000000
xe pipe3_slowfb_NEG $D/pipe3.json --bands $D/slowfb.bands.json --env 10:500
xe ring3_slow_corner $D/ring3.json --bands $D/slow_corner.bands.json
xe ring3_slowfb_NEG $D/ring3.json --bands $D/slowfb.bands.json
for c in bd_c2 bd_c2n_set bd_c3 bd_c4 bd_latch_W2 bd_arbiter; do xe cell_$c $J/$c.json --bands $D/slow_corner.bands.json; done
