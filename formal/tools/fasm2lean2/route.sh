#!/usr/bin/env bash
# Route the fasm2lean2 fixture (link_arb.v: one bd_link W=3 + one bd_arbiter,
# probe C-11c) with the project's flow options (cells/flow.sh: synth_xilinx
# -flatten -nosrl -nolutram -nobram -noclkbuf; nextpnr --ignore-loops), plus --freq
# and a pinned seed (CLAUDE.md).    formal/tools/fasm2lean2/route.sh [SEED]
# Everything goes to build/ (large: synth JSON, frames, .bit; not for git);
# the small, reviewable results are copied to fixture/: the nextpnr FASM, the
# FASM read back from the .bit, the toolchain stamp, the fasm_audit verdict,
# the .bit's sha256, and the SDF (for comparison with the route data).
set -euo pipefail
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
SEED=${1:-1}
OUT=$HERE/build; FIX=$HERE/fixture; mkdir -p "$OUT" "$FIX"
B=$OUT/link_arb_s$SEED
BD_TOOLCHAIN_LOG=$OUT/toolchain.log "$REPO/cells/verify/toolchain.sh" > "$B.toolchain" \
    || { cat "$B.toolchain"; echo "toolchain.sh FAILED: nothing routed here is a result"; exit 1; }
"$TC/openxc7/bin/yosys" -p "
read_verilog -lib -specify $TC/openxc7/share/yosys/xilinx/cells_sim.v
read_verilog $REPO/cells/rtl/bd_ce.v $REPO/cells/rtl/bd_latch.v $REPO/cells/rtl/bd_link.v $REPO/cells/rtl/bd_arb.v $HERE/link_arb.v
synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -top link_arb
write_json $B.json
" > "$B.yosys.log" 2>&1
"$TC/openxc7/bin/nextpnr-xilinx" --chipdb "$TC/openxc7/xc7z010clg400.bin" \
    --xdc "$HERE/link_arb.xdc" --ignore-loops --seed "$SEED" --freq 100 \
    --json "$B.json" --write "$B"_routed.json --sdf "$B.sdf" --fasm "$B.fasm" \
    > "$B.pnr.log" 2>&1 || { tail -30 "$B.pnr.log"; exit 1; }
python3 "$REPO/cells/verify/fasm_audit.py" "$B"_routed.json "$B.fasm" --synth "$B.json" > "$B.audit" 2>&1 \
    || { cat "$B.audit"; echo "fasm_audit FAILED"; exit 1; }
# The bitstream the board would load, exactly as cells/hw/build_hw.sh makes it,
# then read BACK with prjxray's bitread + bit2fasm: fasm2lean is run on the
# disassembled FASM (link_arb_s<SEED>.fromBit.fasm), so the Lean terms come
# from the bits, not from nextpnr's FASM text.
PRJ=$TC/openxc7-src/prjxray; DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PART=xc7z010clg400-1
PYTHONPATH="$PRJ:$PRJ/third_party/fasm:$TC/openxc7/lib/python" python3 -W ignore "$PRJ/utils/fasm2frames.py" \
    --db-root "$DB" --part "$PART" "$B.fasm" > "$B.frames" 2> "$B.frames.log"
"$TC/openxc7/bin/xc7frames2bit" --part_file "$DB/$PART/part.yaml" --part_name "$PART" \
    --frm_file "$B.frames" --output_file "$B.bit" > "$B.bit.log" 2>&1
PYTHONPATH="$PRJ:$PRJ/third_party/fasm" python3 -W ignore "$PRJ/utils/bit2fasm.py" --db-root "$DB" --part "$PART" \
    --bitread "$TC/openxc7/bin/bitread" "$B.bit" > "$B.fromBit.fasm" 2> "$B.bit2fasm.log"
echo "bit $(sha256sum "$B.bit" | cut -c1-16)  $(grep -vc '^\s*$' "$B.fromBit.fasm") features read back"
# The flattened yosys netlist of link_arb, trimmed to the top module (the full
# JSON carries the cells_sim library, ~10 MB): compose.py checks the Lean
# composition (LinkArb.insts) of 11a's per-cell netlists against it.
python3 - "$B.json" > "$FIX/link_arb.synth.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))["modules"]["link_arb"]
keep = {n: {k: c[k] for k in ("type", "parameters", "port_directions", "connections")}
        for n, c in m["cells"].items() if c["type"] != "$scopeinfo"}
print(json.dumps({"ports": m["ports"], "cells": keep}, indent=1, sort_keys=True))
PY
# The placement HINT (cell -> BEL) from nextpnr's routed JSON: used ONLY to
# propose the state-net renaming `rho` that the Lean proof then checks; the
# netlist itself is never taken from it (a wrong hint makes the proof fail).
python3 - "$B"_routed.json > "$B.bels" <<'PY'
import json, sys
m = list(json.load(open(sys.argv[1]))["modules"].values())[0]
for n, c in sorted(m["cells"].items()):
    bel = c.get("attributes", {}).get("NEXTPNR_BEL", "")
    if c["type"] == "SLICE_LUTX":
        base, _, half = n.partition("$")
        site, b = bel.split("/")
        print(base, "O5" if half == "LUT5" or b[1] == "5" else "O6", site, b[0])
PY
for x in fasm fromBit.fasm toolchain audit sdf bels; do cp "$B.$x" "$FIX/link_arb_s$SEED.$x"; done
sha256sum "$B.bit" | sed "s|$OUT/||" > "$FIX/link_arb_s$SEED.bit.sha256"
echo "routed $B.fasm  (nextpnr $(grep sha256 "$B.toolchain" | awk '{print $2}'))"
