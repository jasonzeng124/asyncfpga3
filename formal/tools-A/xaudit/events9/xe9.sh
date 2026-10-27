#!/usr/bin/env bash
# run xevents9 with lean --run on the private overlay /tmp/events9/olean (no lakefile stanza yet)
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/asyncfpga3/formal/lean
FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="/tmp/events9/olean:/tmp/events8/olean:$LEAN_PATH" exec lean --run Formal/Core/XAudit/Events9Main.lean "$@"' sh "$@"
