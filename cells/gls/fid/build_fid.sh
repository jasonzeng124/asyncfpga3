#!/usr/bin/env bash
# Gate-level simulation of the netlist the BOARD runs: rebuilt from the
# bitstream (or a FASM) by fasm2net.py, then the unchanged cells/gls flow.
#
#     cells/gls/fid/build_fid.sh HWDIR WORK [bit|fasm]      default: bit
#
# HWDIR holds one build: <d>.bit, <d>.fasm, <d>_routed.json, <d>.sdf
# (cells/build/hw/<d>/).  The routed JSON is used ONLY for names (the RTL net
# names the testbenches watch, attached by driver bel pin) and to re-key the
# SDF; every connection and every LUT function comes from the bits.
#
# Then:   cells/gls/fid/run_fid.sh WORK          all 16 vectors
#         GATE=1 build_fid.sh ...                also build gate.vvp (the
#                                                ANNOTATE_DONE acceptance gate)
set -euo pipefail
HW=$(cd "$1" && pwd); WORK=$2; SRC=${3:-bit}
D=$(basename "$HW")
HERE=$(cd "$(dirname "$0")" && pwd)
GLS=$(dirname "$HERE")
mkdir -p "$WORK"; WORK=$(cd "$WORK" && pwd)

for f in "$HW/$D.bit" "$HW/$D.fasm" "$HW/${D}_routed.json" "$HW/$D.sdf"; do
    [ -f "$f" ] || { echo "missing $f" >&2; exit 1; }
done
if [ "$SRC" = bit ]; then IN=(--bit "$HW/$D.bit"); else IN=(--fasm "$HW/$D.fasm"); fi

echo "== fasm2net ($SRC) =="
python3 "$HERE/fasm2net.py" "${IN[@]}" --out "$WORK/fid" \
    --names "$HW/${D}_routed.json" --sdf "$HW/$D.sdf"
echo "== equivalence against the routed JSON (information; the sim runs regardless) =="
python3 "$HERE/fasm_equiv.py" "$HW/${D}_routed.json" "$WORK/fid/fasm_routed.json" \
    "$WORK/fid/routes.tsv" "$WORK/fid/stubs.tsv" --out "$WORK/fid/equiv.txt" --max 4 \
    | grep -E "^[0-9]\.|VERDICT" || true

cp "$WORK/fid/fasm_routed.json" "$WORK/routed.json"
cp "$WORK/fid/fasm.sdf" "$WORK/routed.sdf"
{   echo "design:    $D  (FASM-BUILT netlist: fasm2net.py from the $SRC)"
    echo "stamped:   $(date '+%Y-%m-%d %H:%M:%S')"
    for f in "$HW/$D.bit" "$HW/$D.fasm" "$HW/${D}_routed.json" "$HW/$D.sdf"; do
        echo "md5 $(md5sum < "$f" | cut -d' ' -f1)  $f"
    done
    echo "connectivity/LUTs from: $SRC;  names + delays from: routed JSON + SDF (re-keyed)"
    echo "delays:    scale ${GLS_DELAY_SCALE:-1}, scatter sigma ${GLS_SCATTER:-0}, seed ${GLS_SCATTER_SEED:-1}, mode ${GLS_SCATTER_MODE:-arc} (gen.py)"
    if [ -f "$HW/toolchain.txt" ]; then cat "$HW/toolchain.txt"
    else echo "toolchain: UNSTAMPED"; fi
} > "$WORK/provenance.txt"
cat "$WORK/provenance.txt"

export GLS_WORK=$WORK
cd "$WORK"
echo "== gen.py on the FASM-built netlist =="
python3 "$GLS/gen.py"
python3 "$GLS/gen_chan.py"
python3 "$GLS/gen_signals.py"
echo "== compiling =="
if [ "${GATE:-0}" = 1 ]; then
    iverilog -gspecify -I. -o gate.vvp "$GLS/tb_gate.v" netlist.v "$GLS/prims.v"
fi
iverilog -gspecify -DGLS_TRANSPORT_IC -I. -o run_baked.vvp "$GLS/tb_run.v" netlist_baked.v "$GLS/prims.v" 2>&1 \
    | grep -v 'procedural continuous' || true
echo "built $WORK"
