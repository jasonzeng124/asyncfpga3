#!/usr/bin/env bash
# compile one WIP module of probe C8y2 into Wip/C8y2/obj (private olean dir), through slot.sh
# usage: Wip/C8y2/lc.sh KernelCapHist
set -uo pipefail
L=/home/user/asyncfpga3/formal/lean
W=$L/Wip/C8y2
m=$1
cd /home/user/asyncfpga3/formal
# mirror the real build dir by symlinks (Lean resolves a package root in ONE search-path entry)
cp -rsn $L/.lake/build/lib/lean/Formal $W/obj/ 2>/dev/null
rm -f $W/obj/Formal/Net/$m.olean $W/obj/Formal/Net/$m.ilean
./slot.sh lake env bash -c "LEAN_PATH=$W/obj:\$LEAN_PATH lean -DautoImplicit=false --root=$W/src -o $W/obj/Formal/Net/$m.olean $W/src/Formal/Net/$m.lean"
