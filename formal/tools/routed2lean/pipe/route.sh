#!/usr/bin/env bash
# Route the N-stage Muller pipeline exactly like formal/tools/fasm2lean/route.sh
# routes ce_pair (cells/flow.sh options + --freq 100 + pinned seed), then read the
# bits back (fasm2frames -> xc7frames2bit -> bitread/bit2fasm).
#     formal/tools/routed2lean/pipe/route.sh [SEED] [N]
set -euo pipefail
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../../.." && pwd)
SEED=${1:-1}; N=${2:-64}
OUT=$HERE/../build; FIX=$HERE/../fixture; mkdir -p "$OUT" "$FIX"
B=$OUT/muller${N}_s$SEED
BD_TOOLCHAIN_LOG=$OUT/toolchain.log "$REPO/cells/verify/toolchain.sh" > "$B.toolchain" \
    || { cat "$B.toolchain"; echo "toolchain.sh FAILED: nothing routed here is a result"; exit 1; }
"$TC/openxc7/bin/yosys" -p "
read_verilog -lib -specify $TC/openxc7/share/yosys/xilinx/cells_sim.v
read_verilog $REPO/cells/rtl/bd_ce.v $HERE/muller_pipe.v
chparam -set N $N muller_pipe
synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -top muller_pipe
write_json $B.json
" > "$B.yosys.log" 2>&1
"$TC/openxc7/bin/nextpnr-xilinx" --chipdb "$TC/openxc7/xc7z010clg400.bin" \
    --xdc "$HERE/muller_pipe.xdc" --ignore-loops --seed "$SEED" --freq 100 \
    --json "$B.json" --write "$B"_routed.json --sdf "$B.sdf" --fasm "$B.fasm" \
    > "$B.pnr.log" 2>&1 || { tail -30 "$B.pnr.log"; exit 1; }
python3 "$REPO/cells/verify/fasm_audit.py" "$B"_routed.json "$B.fasm" --synth "$B.json" > "$B.audit" 2>&1 \
    || { cat "$B.audit"; echo "fasm_audit FAILED"; exit 1; }
PRJ=$TC/openxc7-src/prjxray; DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PART=xc7z010clg400-1
PYTHONPATH="$PRJ:$PRJ/third_party/fasm:$TC/openxc7/lib/python" python3 -W ignore "$PRJ/utils/fasm2frames.py" \
    --db-root "$DB" --part "$PART" "$B.fasm" > "$B.frames" 2> "$B.frames.log"
"$TC/openxc7/bin/xc7frames2bit" --part_file "$DB/$PART/part.yaml" --part_name "$PART" \
    --frm_file "$B.frames" --output_file "$B.bit" > "$B.bit.log" 2>&1
PYTHONPATH="$PRJ:$PRJ/third_party/fasm" python3 -W ignore "$PRJ/utils/bit2fasm.py" --db-root "$DB" --part "$PART" \
    --bitread "$TC/openxc7/bin/bitread" "$B.bit" > "$B.fromBit.fasm" 2> "$B.bit2fasm.log"
for x in fromBit.fasm toolchain audit sdf; do cp "$B.$x" "$FIX/muller${N}_s$SEED.$x"; done
echo "routed $B.fasm  (nextpnr $(grep sha256 "$B.toolchain" | awk '{print $2}'))"
