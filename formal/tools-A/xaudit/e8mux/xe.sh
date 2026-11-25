#!/usr/bin/env bash
# run xevents8 (Formal/Core/XAudit/Events8Main.lean) with lean --run on the e8mux olean overlay
# (mkolean.sh), through formal/slot.sh.  Args: skel.json bands.json cert.json
OL=${OL:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/e8mux/olean}
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/asyncfpga3/formal/lean
FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="$0:$LEAN_PATH" exec lean -DautoImplicit=false --run Formal/Core/XAudit/Events8Main.lean "$@"' "$OL" "$@"
