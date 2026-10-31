#!/usr/bin/env bash
# xevents5 = the committed Events5Main.lean, through slot.sh.  Uses the native build of mkexe.sh
# (/tmp/kapres/exe/xevents5; output checked byte-identical to `lean --run` on seed 3 slow) when it
# exists, else lean --run on the private olean overlay of mk.sh.
export PATH=$HOME/.elan/bin:$PATH
OL=${OL:-/tmp/kapres/olean}
cd /home/user/asyncfpga3/formal/lean
if [ -x /tmp/kapres/exe/xevents5 ]; then exec ../slot.sh /tmp/kapres/exe/xevents5 "$@"; fi
FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c "LEAN_PATH=\"$OL:\$LEAN_PATH\" exec lean --run Formal/Core/XAudit/Events5Main.lean \"\$@\"" sh "$@"
