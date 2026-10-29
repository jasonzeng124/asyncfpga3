#!/usr/bin/env bash
# usage: build_gls.sh <checkout> <workdir> <sdf>
# r11/build_gls.sh with the route's routed.json taken from <checkout>'s own build
# (cells/build/hw/gcd_hw), mirrors cells/gls/build.sh minus gate.vvp.
set -euo pipefail
CO=$1; WORK=$2; SDF=$3
SRC=$CO/cells/gls
HW=$CO/cells/build/hw/gcd_hw
mkdir -p "$WORK"; cd "$WORK"
cp "$HW/gcd_hw_routed.json" routed.json
cp "$SDF" routed.sdf
md5sum routed.json routed.sdf > provenance.txt
export GLS_WORK=$WORK
python3 "$SRC/gen.py"
python3 "$SRC/gen_probe.py" urig.
python3 "$SRC/gen_chan.py"
python3 "$SRC/gen_signals.py"
iverilog -gspecify -DGLS_TRANSPORT_IC -I. -o run_baked.vvp "$SRC/tb_run.v" netlist_baked.v "$SRC/prims.v" 2>&1 | grep -v 'procedural continuous' || true
ls -la run_baked.vvp
