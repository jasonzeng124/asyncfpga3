#!/usr/bin/env bash
# Full-stack GLS of carry_ro_top's group 0 at one point of the delay band.
#
#   cells/hw/carry_ring/carry_gls.sh FIDDIR WORK FIELD [X Y]
#
# FIDDIR: fasm2net.py --bit <bit> --names <routed.json> --sdf <xray.sdf> output
#   (fasm_routed.json = the netlist decoded from the bits, fasm.sdf = prjxray
#   delays re-keyed onto it).
# FIELD: min (FAST_MIN), max (SLOW_MAX) or band; with band, X = GLS_SDF_BAND
#   (LUT + wire + site pips) and Y = GLS_SDF_BAND_CELL CARRY4=Y,SELMUX2_1=Y.
# GLS_MODEL=fid (transport per-pin arcs, cells/gls/fid_core.vh).  Prints
# RING <slot> <period_ps> <edges> for the eight rings of group 0.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
GLS=$(cd "$HERE/../../gls" && pwd)
FID=$(cd "$1" && pwd); WORK=$2; FIELD=$3; X=${4:-}; Y=${5:-}
mkdir -p "$WORK"; WORK=$(cd "$WORK" && pwd)
cp "$FID/fasm_routed.json" "$WORK/routed.json"
cp "$FID/fasm.sdf" "$WORK/routed.sdf"
unset GLS_SDF_BAND GLS_SDF_BAND_CELL GLS_SDF_BAND_INST GLS_SCATTER GLS_SCATTER_REGION GLS_DELAY_SCALE
export GLS_WORK=$WORK GLS_MODEL=fid GLS_SDF_FIELD=$FIELD
if [ "$FIELD" = band ]; then
    export GLS_SDF_BAND=$X GLS_SDF_BAND_CELL="CARRY4=$Y,SELMUX2_1=$Y"
fi
cd "$WORK"
python3 "$GLS/gen.py" > gen.log 2>&1 || { tail -20 gen.log; exit 1; }
python3 - <<'PY'
m = {}
for ln in open("nets.map"):
    if not ln.startswith("#"):
        w, _, n = ln.strip().partition(" ")
        m.setdefault(n, w)
want = {"HOLD9": "hold[9]"}
want.update({"FB%d" % b: "ring_fb[%d]" % b for b in range(8)})
with open("carry_signals.vh", "w") as f:
    for k, n in want.items():
        f.write("`define %s dut.%s\n" % (k, m[n]))
PY
iverilog -gspecify -DGLS_TRANSPORT_IC -DGLS_FID -I"$GLS" -I. -o carry.vvp \
    "$HERE/tb_carry.v" netlist_baked.v "$GLS/prims.v" 2>&1 | grep -v 'procedural continuous' || true
vvp -n carry.vvp +TEND=${TEND:-3000} +WARM=${WARM:-300} | tee vvp.log | grep -E "^RING|ERROR|rror" || true
grep -q "^RING" vvp.log
