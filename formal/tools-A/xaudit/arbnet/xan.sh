#!/usr/bin/env bash
# Probe E9ArbNet: run xarbnet (Formal/Core/XAudit/Events9ArbNetMain.lean) with lean --run on the overlay $OL
# (oleans of the Events9ArbNet closure; no lakefile stanza).   xan.sh NETLIST.json BANDS.json CERT.json ARB.json
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/asyncfpga3/formal/lean
FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="${OL:?set OL to the overlay}:$LEAN_PATH" exec lean -DautoImplicit=false --run Formal/Core/XAudit/Events9ArbNetMain.lean "$@"' sh "$@"
