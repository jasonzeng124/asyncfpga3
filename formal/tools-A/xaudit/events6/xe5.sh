#!/usr/bin/env bash
# build the private olean overlay first: mk.sh <the Formal/ files of the Check section of A-events6.md>
# run xevents5 with lean --run on the private overlay (no lakefile stanza yet)
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/asyncfpga3/formal/lean
FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="/tmp/events6/olean:$LEAN_PATH" exec lean --run Formal/Core/XAudit/Events5Main.lean "$@"' sh "$@"
