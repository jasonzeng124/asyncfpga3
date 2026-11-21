#!/usr/bin/env bash
# regress.sh TREE HWDIR DESIGN OUT -- the bits-decoded stack up to (not including) iverilog, with the code of TREE:
#   xray_delay.py -> fasm2net.py --ps7 --bit -> fasm_equiv.py -> gen.py (fullstack_dump.sh's band env, no scatter)
# so that two trees (HEAD, patched) can be compared file by file with cmp.
set -uo pipefail
T=$(cd "$1" && pwd); HW=$(cd "$2" && pwd); D=$3; mkdir -p "$4"; O=$(cd "$4" && pwd)
export PYTHONDONTWRITEBYTECODE=1
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}; PX=$TC/openxc7-src/prjxray
G=$T/cells/gls; J=$HW/${D}_routed.json
date -u +"start %FT%TZ" > "$O/times.txt"
if [ -n "${XRAY_SDF_IN:-}" ]; then cp "$XRAY_SDF_IN" "$O/xray.sdf"; echo "xray SDF from $XRAY_SDF_IN" > "$O/xray.log"
else PYTHONPATH=$PX python3 "$G/fid/xray_delay.py" --routed "$J" --sdf "$HW/$D.sdf" --out "$O/xray.sdf" > "$O/xray.log" 2>&1; fi
echo "xray rc=$?" >> "$O/times.txt"; date -u +"xray %FT%TZ" >> "$O/times.txt"
PYTHONPATH=$PX python3 "$G/fid/fasm2net.py" --ps7 --bit "$HW/$D.bit" --out "$O/fid" --names "$J" --sdf "$O/xray.sdf" \
    > "$O/fasm2net.log" 2>&1
echo "fasm2net rc=$?" >> "$O/times.txt"; date -u +"fasm2net %FT%TZ" >> "$O/times.txt"
PYTHONPATH=$PX python3 "$G/fid/fasm_equiv.py" "$J" "$O/fid/fasm_routed.json" "$O/fid/routes.tsv" "$O/fid/stubs.tsv" \
    --out "$O/fid/equiv.txt" --max 4 > "$O/equiv.log" 2>&1
echo "equiv rc=$?" >> "$O/times.txt"; date -u +"equiv %FT%TZ" >> "$O/times.txt"
mkdir -p "$O/gen"
if [ -f "$O/fid/fasm_routed.json" ]; then
  cp "$O/fid/fasm_routed.json" "$O/gen/routed.json"; cp "$O/fid/fasm.sdf" "$O/gen/routed.sdf"
  python3 "$T/research/tools/band_inst_list.py" "$J" '\.chain\.g\[\d+\]\.u$' 0.21 "$O/gen/chains.band" > /dev/null
  ( cd "$O/gen" && GLS_WORK=$O/gen GLS_SDF_FIELD=band GLS_SDF_BAND=0.288 \
      GLS_SDF_BAND_CELL=CARRY4=1,SELMUX2_1=1,SLICE_FFX=1,RAMB18E1_RAMB18E1=1 GLS_SDF_BAND_INST=@$O/gen/chains.band \
      GLS_MODEL=fid PS_DESIGN=$D PYTHONPATH=$PX python3 "$G/gen.py" ) > "$O/gen.log" 2>&1
  echo "gen rc=$?" >> "$O/times.txt"
fi
date -u +"end %FT%TZ" >> "$O/times.txt"
