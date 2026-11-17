#!/usr/bin/env bash
# bench_gate.sh HWDIR DESIGN WORK VECFILE EXPFILE COL -- one full-stack correctness run of a bench route at one corner:
#   COL = max (SLOW_MAX) | min (FAST_MIN) | worst (delay chains 0.21, CARRY4/F7F8/FF 1, rest 0.288, + M scatter:
#   region 0.02, wire 0.126, the measured residual -- JOURNAL 2026-11-04 00:24 / 2026-11-05 00:09)
#   | draw:K (one draw of the parametric delay model, see the case below; JOURNAL 2026-11-16).
# Netlist decoded from the .bit (fasm_equiv verdict), prjxray SDF, fid, ps7_bench.v FIXED mode, +FCLK_PS=12000
# (83.3 MHz), 2 runs per vector.  Verdict: every batch completed 2/2, its runs agreed (mism_st bit 0 clear; added
# 2026-11-16) and odata == EXPFILE line (derived from the C).
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
  draw:*) # one draw of the delay model (PROGRAM 2026-11-16, "the board decides"); parameters from the draw number K,
         # written to $W/draw_K.txt. Source of each range: research/data/fid/ring128 (LUT + wire band 0.2877, p05-p95
         # 0.276-0.303) and research/data/aug_kernels (August kernel builds on the board: x 0.211-0.225); the two disagree,
         # so each class gets its own independent band, uniform over [0.20, 0.31]: delay chains, everything else. CARRY4,
         # F7/F8 and FF were never measured: uniform over [0.20, 1.0]. Within-die: setting M (region 0.02, wire 0.126,
         # wire mode; ring128 README), its own seed per draw.
         K=${COL#draw:}
         # DRAW_CARRY=LO,HI (default 0.20,1.0) narrows the CARRY4 / F7F8 / FF range, e.g. 0.8,1.0 for slow-carry draws
         # (2026-11-17: no August board latency pins that band, PROGRAM "where does the board sit"); the other two
         # bands are drawn exactly as in the default, so draw K differs from the default draw K only in that band.
         DC=${DRAW_CARRY:-0.20,1.0}
         read XC XR XK <<< "$(python3 -c "import random; r=random.Random(7919*$K+17); a=r.uniform(.20,.31); b=r.uniform(.20,.31); u=r.random(); lo,hi=$DC; print(*['%.4f'%v for v in (a, b, lo+u*(hi-lo))])")"
         echo "draw $K chains $XC rest $XR carry/f7f8/ff $XK region 0.02 wire 0.126 seed $K${DRAW_CARRY:+ carry-range $DC}" > "$W/draw_$K.txt"
         python3 "$R/research/tools/band_inst_list.py" "$HW/${D}_routed.json" '\.chain\.g\[\d+\]\.u$' $XC "$W/chains_$K.band" > /dev/null
         export GLS_SDF_FIELD=band GLS_SDF_BAND=$XR GLS_SDF_BAND_CELL=CARRY4=$XK,SELMUX2_1=$XK,SLICE_FFX=$XK \
                GLS_SDF_BAND_INST=@$W/chains_$K.band GLS_SCATTER_REGION=0.02 GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=$K;;
  *) echo "COL?"; exit 2;;
esac
# one compile at a time on the machine: build_ps.sh's iverilog peaks at several GB (OOM kills lose runs)
CD=${COL/:/_}
flock /tmp/eventgraph_compile.lock "$G/ps/build_ps.sh" "$HW" "$W/$CD" "" bit > "$W/$CD.build.log" 2>&1
cd "$W/$CD"; rm -f gate.vvp
vvp run_baked.vvp +FCLK_PS=12000 +MODE=1 +NRUNS=2 +VECFILE="$VEC" +TBATCH=1200000 +TEND=20000000 ${GATE_PLUSARGS:-} > run.log 2>&1 || true   # GATE_PLUSARGS: e.g. +META_INIT=0
rm -f run_baked.vvp
python3 - "$EXP" run.log "$(grep -o 'VERDICT: [A-Z_ ]*' fid/equiv.txt | head -1)" <<'PY'
import sys, re
exp = open(sys.argv[1]).read().split(); got = {}
for l in open(sys.argv[2]):
    if l.startswith("BENCHRES"):
        d = dict(re.findall(r"(\w+)=(\S+)", l)); got[int(d["batch"])] = d
# mism_st bit 0 = the bench's FIXED-mode repeatability latch: the batch's runs did not all return the same value. odata is
# the LAST run's result only, so a wrong first run followed by a right one passed this gate until 2026-11-16 (farm
# steerneg: 5 such runs judged PASS). A batch counts only if every run agreed AND the last one equals the oracle.
mm = [j for j in got if int(got[j].get("mism_st", "0"), 16) & 1]
ok = sum(1 for j, e in enumerate(exp) if j in got and got[j]["odata"] == e and got[j]["completed"] == got[j]["n"]
         and j not in mm)
cyc = sum(int(got[j]["cycles"]) for j in got)
print("%s %d/%d cycles %d %s%s" % ("PASS" if ok == len(exp) else "FAIL", ok, len(exp), cyc, sys.argv[3],
      (" | MISMATCH in batch(es) %s" % ",".join(map(str, sorted(mm)))) if mm else ""))
PY
