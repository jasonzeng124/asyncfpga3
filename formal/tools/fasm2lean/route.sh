#!/usr/bin/env bash
# Route the fasm2lean fixture (ce_pair.v: bd_c2 -> bd_c2n) with the project's
# flow options (cells/flow.sh: synth_xilinx -flatten -nosrl -nolutram -nobram
# -noclkbuf; nextpnr --ignore-loops), plus --freq and a pinned seed (CLAUDE.md).
#     formal/tools/fasm2lean/route.sh [SEED]     -> fixture/ce_pair_s<SEED>.*
set -euo pipefail
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
SEED=${1:-1}
OUT=$HERE/fixture; mkdir -p "$OUT"
B=$OUT/ce_pair_s$SEED
BD_TOOLCHAIN_LOG=$OUT/toolchain.log "$REPO/cells/verify/toolchain.sh" > "$B.toolchain" \
    || { cat "$B.toolchain"; echo "toolchain.sh FAILED: nothing routed here is a result"; exit 1; }
"$TC/openxc7/bin/yosys" -p "
read_verilog -lib -specify $TC/openxc7/share/yosys/xilinx/cells_sim.v
read_verilog $REPO/cells/rtl/bd_ce.v $HERE/ce_pair.v
synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -top ce_pair
write_json $B.json
" > "$B.yosys.log" 2>&1
"$TC/openxc7/bin/nextpnr-xilinx" --chipdb "$TC/openxc7/xc7z010clg400.bin" \
    --xdc "$HERE/ce_pair.xdc" --ignore-loops --seed "$SEED" --freq 100 \
    --json "$B.json" --write "$B"_routed.json --sdf "$B.sdf" --fasm "$B.fasm" \
    > "$B.pnr.log" 2>&1 || { tail -30 "$B.pnr.log"; exit 1; }
python3 "$REPO/cells/verify/fasm_audit.py" "$B"_routed.json "$B.fasm" --synth "$B.json" > "$B.audit" 2>&1 \
    || { cat "$B.audit"; echo "fasm_audit FAILED"; exit 1; }
echo "routed $B.fasm  (nextpnr $(grep sha256 "$B.toolchain" | awk '{print $2}'))"
