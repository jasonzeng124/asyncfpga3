#!/usr/bin/env bash
# bench_gate.sh HWDIR DESIGN WORK VECFILE EXPFILE COL -- one full-stack correctness run of a bench route at one corner:
#   COL = max (SLOW_MAX) | min (FAST_MIN) | worst (delay chains 0.21, CARRY4/F7F8/FF 1, rest 0.288, + M scatter:
#   region 0.02, wire 0.126, the measured residual -- JOURNAL 2026-11-04 00:24 / 2026-11-05 00:09).
# Netlist decoded from the .bit (fasm_equiv verdict), prjxray SDF, fid, ps7_bench.v FIXED mode, +FCLK_PS=12000
# (83.3 MHz), 2 runs per vector.  Verdict: every batch completed 2/2 and odata == EXPFILE line (derived from the C).
set -euo pipefail
HW=$(cd "$1" && pwd); D=$2; mkdir -p "$3"; W=$(cd "$3" && pwd); VEC=$(readlink -f "$4"); EXP=$(readlink -f "$5"); COL=$6
R=$(cd "$(dirname "$0")/../../.." && pwd); G=$R/cells/gls
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}; PX=$TC/openxc7-src/prjxray
XS=$W/xray.sdf
[ -f "$XS" ] || PYTHONPATH=$PX python3 "$G/fid/xray_delay.py" --routed "$HW/${D}_routed.json" --sdf "$HW/$D.sdf" --out "$XS" > "$W/xray.log" 2>&1
export GLS_SDF=$XS GLS_MODEL=fid PS_DESIGN=$D PS_HOST=ps7_bench.v PYTHONPATH=$PX
case $COL in
  max) export GLS_SDF_FIELD=max;; min) export GLS_SDF_FIELD=min;;
  worst) python3 "$R/research/tools/band_inst_list.py" "$HW/${D}_routed.json" '\.chain\.g\[\d+\]\.u$' 0.21 "$W/chains.band" > /dev/null
         export GLS_SDF_FIELD=band GLS_SDF_BAND=0.288 GLS_SDF_BAND_CELL=CARRY4=1,SELMUX2_1=1,SLICE_FFX=1 \
                GLS_SDF_BAND_INST=@$W/chains.band GLS_SCATTER_REGION=0.02 GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=1;;
  *) echo "COL?"; exit 2;;
esac
# one compile at a time on the machine: build_ps.sh's iverilog peaks at several GB (OOM kills lose runs)
flock /tmp/eventgraph_compile.lock "$G/ps/build_ps.sh" "$HW" "$W/$COL" "" bit > "$W/$COL.build.log" 2>&1
cd "$W/$COL"; rm -f gate.vvp
vvp run_baked.vvp +FCLK_PS=12000 +MODE=1 +NRUNS=2 +VECFILE="$VEC" +TBATCH=1200000 +TEND=20000000 > run.log 2>&1 || true
rm -f run_baked.vvp
python3 - "$EXP" run.log "$(grep -o 'VERDICT: [A-Z_ ]*' fid/equiv.txt | head -1)" <<'PY'
import sys, re
exp = open(sys.argv[1]).read().split(); got = {}
for l in open(sys.argv[2]):
    if l.startswith("BENCHRES"):
        d = dict(re.findall(r"(\w+)=(\S+)", l)); got[int(d["batch"])] = d
ok = sum(1 for j, e in enumerate(exp) if j in got and got[j]["odata"] == e and got[j]["completed"] == got[j]["n"])
cyc = sum(int(got[j]["cycles"]) for j in got)
print("%s %d/%d cycles %d %s" % ("PASS" if ok == len(exp) else "FAIL", ok, len(exp), cyc, sys.argv[3]))
PY
