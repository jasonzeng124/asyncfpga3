#!/usr/bin/env bash
# build_ps.sh HWDIR WORK [VECFILE] [bit] -- routed GLS of hw/gcd_ps.v, as cells/gls/build.sh does
# for gcd_hw, with the behavioural PS7 (ps7_master.v) as the only driver.  Env as build.sh/gen.py:
# GLS_SDF (default HWDIR/gcd_ps.sdf), GLS_SDF_FIELD, GLS_MODEL=fid, GLS_SCATTER*, PS_BUNDLE=1.
# PS_DESIGN=gcd_bench_gen PS_HOST=ps7_bench.v: the same for hw/gen_bench.py's bench (HWDIR holds
# gcd_bench_gen.{bit,sdf,_routed.json}; VECFILE unused; run_baked.vvp takes ps7_bench.v's plusargs).
# PS_MON_GEN=<script.py>: run as `script.py ROUTED_JSON nets.map mon_gen.v` after gen.py, and the
# monitor module it writes is compiled into run_baked.vvp (as PS_BUNDLE=1 does with gen_bundle_mon.py).
# With "bit" (the full stack, as fid/build_fid.sh): the netlist is decoded from HWDIR/gcd_ps.bit
# (fasm2net.py --ps7), checked against the routed JSON (fasm_equiv.py, verdict in provenance), and
# GLS_SDF is re-keyed onto it.
# Then: (cd WORK && vvp gate.vvp)  -> must print ANNOTATE_DONE and no SDF WARNING/ERROR;
#       (cd WORK && vvp run_baked.vvp +PSVEC=ps_vec.hex) -> PSRES lines, PSSUMMARY.
set -euo pipefail
HW=$(cd "$1" && pwd); mkdir -p "$2"; WORK=$(cd "$2" && pwd); VEC=${3:-}; SRC=${4:-json}
GLS=$(cd "$(dirname "$0")/.." && pwd); PS=$GLS/ps
D=${PS_DESIGN:-gcd_ps}; HOST=$PS/${PS_HOST:-ps7_master.v}
J=$HW/${D}_routed.json; S=${GLS_SDF:-$HW/$D.sdf}
if [ "$SRC" = bit ]; then
    python3 "$GLS/fid/fasm2net.py" --ps7 --bit "$HW/$D.bit" --out "$WORK/fid" --names "$J" --sdf "$S"
    python3 "$GLS/fid/fasm_equiv.py" "$J" "$WORK/fid/fasm_routed.json" "$WORK/fid/routes.tsv" \
        "$WORK/fid/stubs.tsv" --out "$WORK/fid/equiv.txt" --max 4 | grep -E "VERDICT" || true
    cp "$WORK/fid/fasm_routed.json" "$WORK/routed.json"; cp "$WORK/fid/fasm.sdf" "$WORK/routed.sdf"
else
    cp "$J" "$WORK/routed.json"; cp "$S" "$WORK/routed.sdf"
fi
{   echo "design:    $D (host $(basename "$HOST"))"
    echo "routed.json md5 $(md5sum < "$WORK/routed.json" | cut -d' ' -f1)  <- $J"
    echo "routed.sdf  md5 $(md5sum < "$WORK/routed.sdf" | cut -d' ' -f1)  <- $S, column ${GLS_SDF_FIELD:-min}"
    echo "delays:    scatter ${GLS_SCATTER:-0} region ${GLS_SCATTER_REGION:-0} seed ${GLS_SCATTER_SEED:-1} mode ${GLS_SCATTER_MODE:-arc} logn ${GLS_SCATTER_LOGN:-0}"
    echo "model:     ${GLS_MODEL:-default}"
    echo "netlist:   $SRC$( [ "$SRC" = bit ] && echo " (fasm2net --ps7 from $(md5sum < "$HW/$D.bit" | cut -c1-8)); $(grep -o 'VERDICT.*' "$WORK/fid/equiv.txt")")"
    [ -f "$HW/toolchain.txt" ] && cat "$HW/toolchain.txt" || echo "toolchain: UNSTAMPED"
} > "$WORK/provenance.txt"
cat "$WORK/provenance.txt"
if [ -n "$VEC" ]; then cp "$VEC" "$WORK/ps_vec.hex"; else python3 "$PS/gen_vectors.py" "$WORK/ps_vec.hex"; fi
cd "$WORK"; export GLS_WORK=$WORK
python3 "$GLS/gen.py"
iverilog -gspecify -I. -o gate.vvp "$GLS/tb_gate.v" netlist.v "$GLS/prims.v" "$HOST"
FIDDEF=""; [ "${GLS_MODEL:-}" = fid ] && FIDDEF="-DGLS_FID -I$GLS"
# PS_BUNDLE=1: add gen_bundle_mon.py's out0 bundling monitor (the host cannot see an out0 bundling
# violation: it reads O_DATA two synchronizer clocks after o_req).
MON=""; if [ -n "${PS_MON_GEN:-}" ]; then python3 "$PS_MON_GEN" "$J" nets.map mon_gen.v; MON=mon_gen.v; fi
if [ "${PS_BUNDLE:-0}" = 1 ]; then python3 "$PS/gen_bundle_mon.py" "$J" nets.map bundle_mon.v; MON="$MON bundle_mon.v"; fi
# shellcheck disable=SC2086
iverilog -gspecify -DGLS_TRANSPORT_IC $FIDDEF -I. -o run_baked.vvp "$PS/tb_ps.v" netlist_baked.v "$GLS/prims.v" "$HOST" $MON 2>&1 \
    | grep -v 'procedural continuous' || true
echo "built in $WORK"
