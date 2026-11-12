#!/usr/bin/env bash
# Probe C-10f: route the N-stage Muller pipeline of 10d (formal/tools/routed2lean/pipe/,
# read-only) on one placer seed, into formal/tools/rtfb/build/ (not 10d's build/fixture).
# Same invocation as 10d's pipe/route.sh: cells/flow.sh options + --freq 100 + --seed,
# fasm_audit, then the bits are written and read back (bit2fasm).
#     formal/tools/rtfb/route_muller.sh SEED [N]
set -euo pipefail
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
PIPE=$REPO/formal/tools/routed2lean/pipe
SEED=${1:?seed}; N=${2:-64}
OUT=$HERE/build/muller; mkdir -p "$OUT"
B=$OUT/muller${N}_s$SEED
BD_TOOLCHAIN_LOG=$OUT/toolchain.log "$REPO/cells/verify/toolchain.sh" > "$B.toolchain" \
    || { cat "$B.toolchain"; echo "toolchain.sh FAILED: nothing routed here is a result"; exit 1; }
printf 'nextpnr sha256 %s\n' "$(sha256sum "$TC/openxc7/bin/nextpnr-xilinx" | cut -c1-16)" >> "$B.toolchain"
"$TC/openxc7/bin/yosys" -p "
read_verilog -lib -specify $TC/openxc7/share/yosys/xilinx/cells_sim.v
read_verilog $REPO/cells/rtl/bd_ce.v $PIPE/muller_pipe.v
chparam -set N $N muller_pipe
synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -top muller_pipe
write_json $B.json
" > "$B.yosys.log" 2>&1
"$TC/openxc7/bin/nextpnr-xilinx" --chipdb "$TC/openxc7/xc7z010clg400.bin" \
    --xdc "$PIPE/muller_pipe.xdc" --ignore-loops --seed "$SEED" --freq 100 \
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
sha256sum "$B.fasm" "$B.fromBit.fasm" > "$B.sha"
echo "routed $B  (nextpnr $(tail -1 "$B.toolchain" | awk '{print $3}'), audit: $(tail -1 "$B.audit")"
