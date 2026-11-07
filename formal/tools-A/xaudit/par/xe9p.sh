#!/usr/bin/env bash
# Probe E9Par: run xevents9par (Formal/Core/XAudit/Events9ParMain.lean) with lean --run on the overlay $OL
# (oleans of the Events9Par closure; no lakefile stanza).   xe9p.sh NETLIST.json BANDS.json CERT.json
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/asyncfpga3/formal/lean
FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="${OL:?set OL to the overlay}:$LEAN_PATH" exec lean -DautoImplicit=false --run Formal/Core/XAudit/Events9ParMain.lean "$@"' sh "$@"
