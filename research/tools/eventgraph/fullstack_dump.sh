#!/usr/bin/env bash
# fullstack_dump.sh HWDIR DESIGN WORK VECFILE -- the itercost full-stack run (research/data/itercost/README.md), with
# every top-level net of the decoded netlist dumped to WORK/dump.vcd for trace.py / eventgraph.py.
#   HWDIR holds DESIGN.{bit,sdf,_routed.json} (e.g. cells/build/hw/xorshift_bench_gen, DESIGN=xorshift_bench_gen).
#   Stack: netlist decoded from the .bit (fasm2net --ps7, fasm_equiv verdict in WORK/provenance.txt), prjxray SDF
#   (xray_delay.py), GLS_MODEL=fid, the calibrated bands with no scatter: delay chains 0.21, CARRY4/F7F8/FF at 1
#   (SLOW_MAX), everything else 0.288 -- the full stack's `worst` column without scatter.
#   Run: ps7_bench.v, +FCLK_PS=12000, +MODE=1 (FIXED), +NRUNS=2, one batch per VECFILE line.
# (The 2026-11-08 itercost runs used a dump top that was not committed; this file replaces it.)
set -euo pipefail
HW=$(cd "$1" && pwd); D=$2; mkdir -p "$3"; W=$(cd "$3" && pwd); VEC=$(readlink -f "$4")
R=$(cd "$(dirname "$0")/../../.." && pwd); G=$R/cells/gls
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}; PX=$TC/openxc7-src/prjxray
XS=$W/xray.sdf
# XRAY_SDF_IN: use this prjxray SDF instead of computing one (e.g. an SDF with a constructed defect, sdf_inject.py)
if [ -n "${XRAY_SDF_IN:-}" ]; then cp "$XRAY_SDF_IN" "$XS"; echo "xray SDF from $XRAY_SDF_IN" > "$W/xray.log"
else PYTHONPATH=$PX python3 "$G/fid/xray_delay.py" --routed "$HW/${D}_routed.json" --sdf "$HW/$D.sdf" --out "$XS" > "$W/xray.log" 2>&1; fi
python3 "$R/research/tools/band_inst_list.py" "$HW/${D}_routed.json" '\.chain\.g\[\d+\]\.u$' 0.21 "$W/chains.band" > /dev/null
export GLS_SDF=$XS GLS_SDF_FIELD=${DUMP_FIELD:-band} GLS_SDF_BAND=0.288 GLS_SDF_BAND_CELL=CARRY4=1,SELMUX2_1=1,SLICE_FFX=1,RAMB18E1_RAMB18E1=1 \
       GLS_SDF_BAND_INST=@$W/chains.band GLS_MODEL=fid PS_DESIGN=$D PS_HOST=ps7_bench.v PYTHONPATH=$PX
# DUMP_FIELD=min|max: a prjxray corner column instead of the calibrated bands (no band settings with it; gen.py refuses)
if [ "${DUMP_FIELD:-band}" != band ]; then unset GLS_SDF_BAND GLS_SDF_BAND_CELL GLS_SDF_BAND_INST; export GLS_SDF_FIELD=$DUMP_FIELD; fi
# one compile at a time on the machine: build_ps.sh's iverilog peaks at several GB (OOM kills lose runs)
"$R/research/tools/compile_slot.sh" "$G/ps/build_ps.sh" "$HW" "$W" "" bit > "$W/build.log" 2>&1
rm -f "$W/run_baked.vvp" "$W/gate.vvp"
cat > "$W/dump.v" <<'V'
module dump_all; initial begin $dumpfile("dump.vcd"); $dumpvars(1, tb_ps.dut); end endmodule
V
cd "$W"
"$R/research/tools/compile_slot.sh" iverilog -gspecify -DGLS_TRANSPORT_IC -DGLS_FID -I"$G" -I. -o run.vvp "$G/ps/tb_ps.v" netlist_baked.v "$G/prims.v" \
    "$G/ps/ps7_bench.v" dump.v 2>&1 | grep -v 'procedural continuous' || true
vvp run.vvp +FCLK_PS=12000 +MODE=1 +NRUNS=2 +VECFILE="$VEC" +TBATCH=1200000 +TEND=3000000 ${GATE_PLUSARGS:-} > run.log 2>&1 || true
rm -f run.vvp
grep -o "VERDICT.*" fid/equiv.txt || true
grep BENCHRES run.log | sed 's/sig=[0-9a-f]* //' | cut -c1-200 || echo "NO BENCHRES"
