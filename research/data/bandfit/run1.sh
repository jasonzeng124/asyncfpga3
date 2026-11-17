#!/usr/bin/env bash
# run1.sh KERNEL X Y TAG [VECFILE] -- one full-stack run of the August KERNEL_bench_gen build (netlist from its .bit,
# prjxray SDF, GLS_MODEL=fid, ps7_bench.v FIXED mode, +FCLK_PS=10000 as research/data/aug_kernels) at band X for
# LUT + interconnect and band Y for CARRY4 / SELMUX2_1 / SLICE_FFX IOPATH arcs. Log kept: BENCHRES lines + provenance.
set -euo pipefail
K=$1; X=$2; Y=$3; TAG=$4
R=/home/user/asyncfpga3; G=$R/cells/gls; B=/tmp/claude-0/bandfit
D=${K}_bench_gen; HW=$B/hw/$D; VEC=${5:-$B/vec/$K.hex}
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}; PX=$TC/openxc7-src/prjxray
if [ ! -f "$HW/xray.sdf" ]; then
  mkdir -p "$HW"; S=$R/research/board/aug/builds/$D
  for f in $D.bit $D.sdf ${D}_routed.json; do xz -dc "$S/$f.xz" > "$HW/$f"; done
  PYTHONPATH=$PX python3 "$G/fid/xray_delay.py" --routed "$HW/${D}_routed.json" --sdf "$HW/$D.sdf" --out "$HW/xray.sdf.tmp" > "$HW/xray.log" 2>&1
  mv "$HW/xray.sdf.tmp" "$HW/xray.sdf"
fi
W=$B/work/${K}_$TAG; rm -rf "$W"; mkdir -p "$W"
export GLS_SDF=$HW/xray.sdf GLS_MODEL=fid PS_DESIGN=$D PS_HOST=ps7_bench.v PYTHONPATH=$PX
export GLS_SDF_FIELD=band GLS_SDF_BAND=$X GLS_SDF_BAND_CELL=CARRY4=$Y,SELMUX2_1=$Y,SLICE_FFX=$Y
t0=$(date +%s)
flock /tmp/eventgraph_compile.lock "$G/ps/build_ps.sh" "$HW" "$W" "" bit > "$W/build.log" 2>&1
t1=$(date +%s)
cd "$W"; rm -f gate.vvp
vvp run_baked.vvp +FCLK_PS=10000 +MODE=1 +NRUNS=2 +VECFILE="$VEC" +TEND=20000000 > run.log 2>&1 || true
t2=$(date +%s)
O=$B/logs/${K}_$TAG.log; mkdir -p $B/logs
{ echo "# run1.sh $K x=$X y=$Y vec=$(basename $VEC) build ${t1}-${t0}s run $((t2-t1))s"; cat provenance.txt | sed 's/^/# /'
  grep -h "GLS_SDF_BAND_CELL\|ANNOTATE_DONE\|WARNING\|ERROR" build.log run.log | head -5 | sed 's/^/# /'
  grep -E "^BENCH" run.log; } > "$O"
rm -f run_baked.vvp netlist_baked.v netlist.v
echo "done $O"
