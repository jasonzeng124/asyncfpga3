#!/usr/bin/env bash
# memport_gate.sh HWDIR WORK [VAR=VALUE ...] -- the RAMB18E1 self-test of the bits-decoded full stack (README.md here):
# cells/hw/mem_port_ps.v (bd_mem through its real handshake, a BIST in the aclk domain) built by cells/hw/build_mem.sh
# into HWDIR, decoded from HWDIR/mem_port_ps.bit (fasm2net.py --ps7), checked against the routed JSON (fasm_equiv.py),
# prjxray SDF (xray_delay.py), fid model, at research/tools/eventgraph/bench_gate.sh's `worst` corner (chains 0.21,
# CARRY4/F7F8/FF 1, rest 0.288, + M scatter) with the RAMB18E1 clock-to-out at the slow end too (BAND_CELL= overrides),
# host = ps7_memport.v (gen_ps7_memport.py), FCLK 83.3 MHz.  VAR=VALUE pairs are exported before the build (e.g.
# GLS_SCALE_INST=...); WORK/xray.sdf, if it exists, is used as the SDF (a negative control edits it).
# Prints the gate.vvp annotate check, the MEMPORT line, the violation counts and the equivalence verdict.
set -euo pipefail
HW=$(cd "$1" && pwd); mkdir -p "$2"; W=$(cd "$2" && pwd); shift 2
R=$(cd "$(dirname "$0")/../../../.." && pwd); G=$R/cells/gls; D=mem_port_ps
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}; PX=$TC/openxc7-src/prjxray
XS=$W/xray.sdf
[ -f "$XS" ] || PYTHONPATH=$PX python3 "$G/fid/xray_delay.py" --routed "$HW/${D}_routed.json" --sdf "$HW/$D.sdf" --out "$XS" > "$W/xray.log" 2>&1
python3 "$R/research/tools/band_inst_list.py" "$HW/${D}_routed.json" '\.chain\.g\[\d+\]\.u$' 0.21 "$W/chains.band" > /dev/null
export GLS_SDF=$XS GLS_MODEL=fid PS_DESIGN=$D PS_HOST=../fid/bram/ps7_memport.v PYTHONPATH=$PX
export GLS_SDF_FIELD=band GLS_SDF_BAND=0.288 GLS_SDF_BAND_CELL=${BAND_CELL:-CARRY4=1,SELMUX2_1=1,SLICE_FFX=1,RAMB18E1_RAMB18E1=1} \
       GLS_SDF_BAND_INST=@$W/chains.band GLS_SCATTER_REGION=0.02 GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=1
for kv in "$@"; do export "${kv?}"; done
"$R/research/tools/compile_slot.sh" "$G/ps/build_ps.sh" "$HW" "$W/run" "" bit > "$W/build.log" 2>&1
cd "$W/run"
vvp gate.vvp > gate.log 2>&1 || true
echo "gate: $(grep -c ANNOTATE_DONE gate.log) ANNOTATE_DONE, $(grep -ci 'warning' gate.log) warning line(s), $(grep -ci 'error' gate.log) error line(s)"
rm -f gate.vvp
vvp run_baked.vvp +FCLK_PS=12000 +TEND=${TEND_NS:-30000000} +TMEM=${TMEM_NS:-25000000} > run.log 2>&1 || true
rm -f run_baked.vvp netlist_baked.v
grep -E "MEMPORT" run.log || echo "MEMPORT line missing (see $W/run/run.log)"
echo "RAMB18 violations: $(grep -c 'RAMB18 .*VIOLATION' run.log)  FF violations: $(grep -c 'FF .*VIOLATION' run.log)"
grep -o "VERDICT.*" fid/equiv.txt
