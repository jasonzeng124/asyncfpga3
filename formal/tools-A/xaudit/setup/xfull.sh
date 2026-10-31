#!/usr/bin/env bash
# Probe E9Setup: run xfull (Formal/Core/XAudit/Events9FullMain.lean) with lean --run on the overlay $OL.
#   xfull.sh SKEL.json BANDS.json CERT.json MAP.json
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/asyncfpga3/formal/lean
FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="${OL:?set OL to the overlay}:$LEAN_PATH" exec lean -DautoImplicit=false --run Formal/Core/XAudit/Events9FullMain.lean "$@"' sh "$@"
