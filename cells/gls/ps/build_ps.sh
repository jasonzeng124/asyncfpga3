#!/usr/bin/env bash
# build_ps.sh HWDIR WORK [VECFILE] -- routed GLS of hw/gcd_ps.v, as cells/gls/build.sh does for
# gcd_hw, with the behavioural PS7 (ps7_master.v) as the only driver.  Env as build.sh/gen.py:
# GLS_SDF (default HWDIR/gcd_ps.sdf), GLS_SDF_FIELD, GLS_MODEL=fid, GLS_SCATTER*.
# Then: (cd WORK && vvp gate.vvp)  -> must print ANNOTATE_DONE and no SDF WARNING/ERROR;
#       (cd WORK && vvp run_baked.vvp +PSVEC=ps_vec.hex) -> PSRES lines, PSSUMMARY.
set -euo pipefail
HW=$(cd "$1" && pwd); mkdir -p "$2"; WORK=$(cd "$2" && pwd); VEC=${3:-}
GLS=$(cd "$(dirname "$0")/.." && pwd); PS=$GLS/ps
J=$HW/gcd_ps_routed.json; S=${GLS_SDF:-$HW/gcd_ps.sdf}
cp "$J" "$WORK/routed.json"; cp "$S" "$WORK/routed.sdf"
{   echo "design:    gcd_ps"
    echo "routed.json md5 $(md5sum < "$WORK/routed.json" | cut -d' ' -f1)  <- $J"
    echo "routed.sdf  md5 $(md5sum < "$WORK/routed.sdf" | cut -d' ' -f1)  <- $S, column ${GLS_SDF_FIELD:-min}"
    echo "delays:    scatter ${GLS_SCATTER:-0} region ${GLS_SCATTER_REGION:-0} seed ${GLS_SCATTER_SEED:-1} mode ${GLS_SCATTER_MODE:-arc} logn ${GLS_SCATTER_LOGN:-0}"
    echo "model:     ${GLS_MODEL:-default}"
    [ -f "$HW/toolchain.txt" ] && cat "$HW/toolchain.txt" || echo "toolchain: UNSTAMPED"
} > "$WORK/provenance.txt"
cat "$WORK/provenance.txt"
if [ -n "$VEC" ]; then cp "$VEC" "$WORK/ps_vec.hex"; else python3 "$PS/gen_vectors.py" "$WORK/ps_vec.hex"; fi
cd "$WORK"; export GLS_WORK=$WORK
python3 "$GLS/gen.py"
iverilog -gspecify -I. -o gate.vvp "$GLS/tb_gate.v" netlist.v "$GLS/prims.v" "$PS/ps7_master.v"
FIDDEF=""; [ "${GLS_MODEL:-}" = fid ] && FIDDEF="-DGLS_FID -I$GLS"
# shellcheck disable=SC2086
iverilog -gspecify -DGLS_TRANSPORT_IC $FIDDEF -I. -o run_baked.vvp "$PS/tb_ps.v" netlist_baked.v "$GLS/prims.v" "$PS/ps7_master.v" 2>&1 \
    | grep -v 'procedural continuous' || true
echo "built in $WORK"
