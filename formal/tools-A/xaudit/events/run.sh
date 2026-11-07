#!/usr/bin/env bash
# Build the Events modules into a private olean dir (no lake build) and run
# xevents (interpreter) on the designs; write results here. From anywhere:
#   formal/tools-A/xaudit/events/run.sh
# Once the lead adds the [[lean_exe]] stanza (name "xevents", root
# "Formal.Core.XAudit.EventsMain"), `lake exe xevents ARGS` replaces this.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
L="$(cd "$HERE/../../../lean" && pwd)"
export XAUDIT_OLEAN="${EVENTS_OLEAN:-/tmp/events/olean}"
export PATH=$HOME/.elan/bin:$PATH
cd "$L"
for f in Events EventsRing EventsDesign EventsMain; do
  ../tools-A/xaudit/lean.sh Formal/Core/XAudit/$f.lean
done
D=../tools-A/xaudit/designs
xe() { ../slot.sh lake env bash -c "LEAN_PATH=$XAUDIT_OLEAN:\$LEAN_PATH lean --run Formal/Core/XAudit/EventsMain.lean $*" || true; }
xe $D/ring3.json --bands $D/slow_corner.bands.json > "$HERE/ring3_slow_corner.txt"
xe $D/ring3.json --bands $D/slowfb.bands.json > "$HERE/ring3_slowfb.txt"
xe $D/pipe3.json --bands $D/slow_corner.bands.json > "$HERE/pipe3_slow_corner.txt"
cd "$HERE"
{ python3 -I ring3_sim.py 200; for h in 81 85; do python3 -I ring3_sim.py 40 $h $h; done; python3 -I ring3_sim.py 100 130 150; } > ring3_sim.txt
tail -n 2 ring3_slow_corner.txt ring3_slowfb.txt pipe3_slow_corner.txt; cat ring3_sim.txt
