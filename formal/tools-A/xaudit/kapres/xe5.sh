#!/usr/bin/env bash
# xevents5 (committed Events5Main.lean) via lean --run on the private overlay, through slot.sh.
export PATH=$HOME/.elan/bin:$PATH
OL=${OL:-/tmp/kapres/olean}
cd /home/user/asyncfpga3/formal/lean
FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c "LEAN_PATH=\"$OL:\$LEAN_PATH\" exec lean --run Formal/Core/XAudit/Events5Main.lean \"\$@\"" sh "$@"
