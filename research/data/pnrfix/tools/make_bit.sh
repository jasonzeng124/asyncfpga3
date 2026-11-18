#!/usr/bin/env bash
# make_bit.sh RUNDIR TOP -- RUNDIR/TOP.fasm -> RUNDIR/TOP.bit with build_bench.sh's recipe (fasm2frames + xc7frames2bit)
set -euo pipefail
D=$1; T=$2
PX=$TC/openxc7-src/prjxray; DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PART=xc7z010clg400-1
PYTHONPATH="$PX:$TC/openxc7/lib/python" python3 "$PX/utils/fasm2frames.py" --db-root "$DB" --part "$PART" "$D/$T.fasm" > "$D/$T.frames" 2> "$D/frames.log"
$TC/openxc7/bin/xc7frames2bit --part_file "$DB/$PART/part.yaml" --part_name "$PART" --frm_file "$D/$T.frames" --output_file "$D/$T.bit" > "$D/bit.log" 2>&1
rm -f "$D/$T.frames"; ls -la "$D/$T.bit" | awk '{print $5, $9}'
