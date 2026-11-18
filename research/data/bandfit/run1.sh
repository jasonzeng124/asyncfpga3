#!/usr/bin/env bash
# run1.sh KERNEL X Y TAG [VECFILE] -- one full-stack run of the August KERNEL_bench_gen build (netlist from its .bit,
# prjxray SDF, GLS_MODEL=fid, ps7_bench.v FIXED mode, +FCLK_PS=10000 as research/data/aug_kernels) at band X for
# LUT + interconnect and band Y for CARRY4 / SELMUX2_1 / SLICE_FFX IOPATH arcs. Log kept: BENCHRES lines + provenance.
# Paths: the repo is this script's ../../..; work under $RUNS/bandfit (RUNS must be set); the GLS compile holds one of
# research/tools/compile_slot.sh's machine-wide slots; the HW dir (bits, SDF, xray SDF) is made once under a flock.
# FCLK_PS: the host's aclk period in ps; default the VECFILE's sidecar NAME.fclk_ps if there is one (the FCLK0 the
# board logs of those vectors were taken at), else 10000 (100 MHz, every vector file here).
# vvp runs line-buffered (stdbuf -oL), so run.log shows each BENCHRES as its batch ends.
# Y > 1 extrapolates past SLOW_MAX (gen.py: fast_min + y * (slow_max - fast_min)); it is not a prjxray corner.
set -euo pipefail
K=$1; X=$2; Y=$3; TAG=$4
R=$(cd "$(dirname "$0")/../../.." && pwd); G=$R/cells/gls; B=${RUNS:?RUNS must be set}/bandfit
D=${K}_bench_gen; HW=$B/hw/$D; VEC=${5:-$R/research/data/bandfit/vec/$K.hex}
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}; PX=$TC/openxc7-src/prjxray
FCLK_PS=${FCLK_PS:-$(cat "${VEC%.hex}.fclk_ps" 2>/dev/null || echo 10000)}
mkdir -p "$B/hw"
(
  flock 9
  if [ ! -f "$HW/xray.sdf" ]; then
    mkdir -p "$HW"; S=$R/research/board/aug/builds/$D
    for f in $D.bit $D.sdf ${D}_routed.json; do xz -dc "$S/$f.xz" > "$HW/$f"; done
    [ -f "$S/toolchain.txt" ] && cp "$S/toolchain.txt" "$HW/toolchain.txt"
    PYTHONPATH=$PX python3 "$G/fid/xray_delay.py" --routed "$HW/${D}_routed.json" --sdf "$HW/$D.sdf" --out "$HW/xray.sdf.tmp" > "$HW/xray.log" 2>&1
    mv "$HW/xray.sdf.tmp" "$HW/xray.sdf"
  fi
) 9> "$B/hw/$D.lock"
W=$B/work/${K}_$TAG; rm -rf "$W"; mkdir -p "$W"
export GLS_SDF=$HW/xray.sdf GLS_MODEL=fid PS_DESIGN=$D PS_HOST=ps7_bench.v PYTHONPATH=$PX
export GLS_SDF_FIELD=band GLS_SDF_BAND=$X GLS_SDF_BAND_CELL=CARRY4=$Y,SELMUX2_1=$Y,SLICE_FFX=$Y
# LATMON=1 (default): compile in lat_mon.py's monitor, which prints each call's kernel latency in ps (LATMON lines;
# the bench's latmin is in 10 ns aclk cycles). LATMON=0 reproduces the runs made before it.
[ "${LATMON:-1}" = 1 ] && export PS_MON_GEN=$R/research/data/bandfit/lat_mon.py
t0=$(date +%s)
"$R/research/tools/compile_slot.sh" "$G/ps/build_ps.sh" "$HW" "$W" "" bit > "$W/build.log" 2>&1
t1=$(date +%s)
cd "$W"; [ "${GATE:-0}" = 1 ] || rm -f gate.vvp
stdbuf -oL vvp run_baked.vvp +FCLK_PS=$FCLK_PS +MODE=1 +NRUNS=2 +VECFILE="$VEC" +TEND=20000000 > run.log 2>&1 || true
t2=$(date +%s)
# GATE=1: also the ANNOTATE_DONE acceptance gate (iverilog's own $sdf_annotate of gen.py's annot.sdf on netlist.v;
# the key matching does not depend on X / Y, so once per kernel is enough). Its SDF WARNING/ERROR count is logged.
if [ "${GATE:-0}" = 1 ]; then vvp gate.vvp > gate.log 2>&1 || true; fi
O=$B/logs/${K}_$TAG.log; mkdir -p "$B/logs"
{ echo "# run1.sh $K x=$X y=$Y vec=$(basename "$VEC") fclk_ps=$FCLK_PS build $((t1-t0))s run $((t2-t1))s host $(hostname -s)"; sed 's/^/# /' provenance.txt
  grep -h "GLS_SDF_BAND_CELL\|IOPATH  claimed\|WARNING\|ERROR" build.log run.log | head -6 | sed 's/^/# /'
  if [ -f gate.log ]; then echo "# gate: $(grep -c ANNOTATE_DONE gate.log) ANNOTATE_DONE, $(grep -c 'SDF WARNING\|SDF ERROR' gate.log) SDF WARNING/ERROR lines"; fi
  grep -E "^BENCH|^LATMON|^lat_mon" run.log build.log -h; } > "$O"
rm -f run_baked.vvp gate.vvp netlist_baked.v netlist.v
echo "done $O"
