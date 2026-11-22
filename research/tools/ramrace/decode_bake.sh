#!/usr/bin/env bash
# decode_bake.sh HW D OUT XC XR XK [K]  -- the decoded netlist of route HW/D (fasm2net --ps7 from the .bit, as
# build_ps.sh "bit"), its prjxray SDF (xray_delay.py), then cells/gls/gen.py at one point of the delay model: chains
# XC, the rest XR, CARRY4/F7F8/FF/RAMB18E1 XK; with K the draw's scatter (region 0.02, wire 0.126, seed K), without K
# none.  Leaves OUT/{routed.json, netlist_baked.v, nets.map, names.map} for ram_race.py / race_mc.py.  No simulation.
set -euo pipefail
HW=$1; D=$2; O=$3; XC=$4; XR=$5; XK=$6; K=${7:-}
R=$(cd "$(dirname "$0")/../../.." && pwd); G=$R/cells/gls; PX=${TC:-$HOME/dev2/lib/fpgatoolchain}/openxc7-src/prjxray
mkdir -p "$O"; O=$(cd "$O" && pwd); HW=$(cd "$HW" && pwd)
[ -f "$O/xray.sdf" ] || PYTHONPATH=$PX python3 "$G/fid/xray_delay.py" --routed "$HW/${D}_routed.json" --sdf "$HW/$D.sdf" --out "$O/xray.sdf" > "$O/xray.log" 2>&1
if [ ! -f "$O/routed.json" ]; then
  PYTHONPATH=$PX python3 "$G/fid/fasm2net.py" --ps7 --bit "$HW/$D.bit" --out "$O/fid" --names "$HW/${D}_routed.json" --sdf "$O/xray.sdf" > "$O/fasm2net.log" 2>&1
  cp "$O/fid/fasm_routed.json" "$O/routed.json"; cp "$O/fid/fasm.sdf" "$O/routed.sdf"
fi
python3 "$R/research/tools/band_inst_list.py" "$HW/${D}_routed.json" '\.chain\.g\[\d+\]\.u$' $XC "$O/chains.band" > /dev/null
export GLS_WORK=$O GLS_MODEL=fid PYTHONPATH=$PX GLS_SDF_FIELD=band GLS_SDF_BAND=$XR \
  GLS_SDF_BAND_CELL=CARRY4=$XK,SELMUX2_1=$XK,SLICE_FFX=$XK,RAMB18E1_RAMB18E1=$XK GLS_SDF_BAND_INST=@$O/chains.band
if [ -n "$K" ]; then export GLS_SCATTER_REGION=0.02 GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=$K; fi
( cd "$O" && python3 "$G/gen.py" > gen.log 2>&1 )
rm -f "$O/netlist.v" "$O/annot.sdf"
echo "$XC $XR $XK ${K:-noscatter}" > "$O/point.txt"
