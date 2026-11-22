#!/usr/bin/env bash
# fasm_to_equiv.sh FASM ROUTED_JSON SDF WORK -- FASM -> .bit (fasm2frames + xc7frames2bit, build_bench.sh's recipe)
# -> fasm2net --ps7 decode -> fasm_equiv (the clone's) -> WORK/fid/equiv.txt
set -euo pipefail
FASM=$(readlink -f $1); J=$(readlink -f $2); S=$(readlink -f $3); W=$4; mkdir -p "$W"; W=$(cd "$W" && pwd)
PX=$TC/openxc7-src/prjxray; DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PART=xc7z010clg400-1
R=/tmp/bot/sa/pnrfix/repo
PYTHONPATH="$PX:$TC/openxc7/lib/python" python3 "$PX/utils/fasm2frames.py" --db-root "$DB" --part "$PART" "$FASM" > "$W/x.frames" 2> "$W/frames.log"
$TC/openxc7/bin/xc7frames2bit --part_file "$DB/$PART/part.yaml" --part_name "$PART" --frm_file "$W/x.frames" --output_file "$W/x.bit" > "$W/bit.log" 2>&1
rm -f "$W/x.frames"
PYTHONPATH=$PX python3 "$R/cells/gls/fid/fasm2net.py" --ps7 --bit "$W/x.bit" --out "$W/fid" --names "$J" --sdf "$S" > "$W/fasm2net.log" 2>&1
PYTHONPATH=$PX python3 "$R/cells/gls/fid/fasm_equiv.py" "$J" "$W/fid/fasm_routed.json" "$W/fid/routes.tsv" "$W/fid/stubs.tsv" --out "$W/fid/equiv.txt" --max 4 | tail -1
