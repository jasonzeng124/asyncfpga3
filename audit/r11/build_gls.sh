#!/usr/bin/env bash
# usage: build_gls.sh <checkout> <workdir> <sdf> [fid]
# mirrors cells/gls/build.sh minus gate.vvp; work dir outside the checkout
set -euo pipefail
CO=$1; WORK=$2; SDF=$3; FID=${4:-}
SRC=$CO/cells/gls
HW=$HOME/wt-r7x/cells/build/hw/gcd_hw
mkdir -p "$WORK"; cd "$WORK"
cp "$HW/gcd_hw_routed.json" routed.json
cp "$SDF" routed.sdf
md5sum routed.json routed.sdf > provenance.txt
export GLS_WORK=$WORK
python3 "$SRC/gen.py"
python3 "$SRC/gen_probe.py" urig.
python3 "$SRC/gen_chan.py"
python3 "$SRC/gen_signals.py"
FIDDEF=""; [ "$FID" = fid ] && FIDDEF="-DGLS_FID -I$SRC"
iverilog -gspecify -DGLS_TRANSPORT_IC $FIDDEF -I. -o run_baked.vvp "$SRC/tb_run.v" netlist_baked.v "$SRC/prims.v" 2>&1 | grep -v 'procedural continuous' || true
ls -la run_baked.vvp
