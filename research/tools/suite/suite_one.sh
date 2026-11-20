#!/usr/bin/env bash
# suite_one.sh KERNEL SEED [NDRAWS] [MAXIT] -- one kernel of the compiler suite through the automatic path, one placer
# seed (PROGRAM "A benchmark suite for the compiler", owner 2026-11-17).  Nothing here is set for a kernel by name except
# where its verification data lives (vectors, oracle), which is per kernel by nature.
#   1. research/tools/auto/auto_size.sh: BDC_AUTO=1, sizes from the one rule (corner_audit CA_SIZERULE=1) on the route
#      as built, re-route and ratchet until the rule is clean on its own route or MAXIT routes were built.  The static
#      rule is a tool here, not a gate (PROGRAM "The board decides"): a NOT CLEAN loop still goes to the draws.
#   2. the bits: fasm_equiv EQUIVALENT and ffmux_scan clean, else the route is not a board route (reported, not judged).
#   3. NDRAWS draws of the delay model (bench_gate.sh draw:K, K = 10000 + 100 * SEED + j: a different model point on
#      every route), the kernel's vectors, expected values compiled from the C at run time (never recorded from a run).
#   4. metrics: P (timed event graph on the period vector), latency per call (BENCHRES, host cycles of 12 ns), kernel
#      LUTs (SLICE_LUTX cells under the DUT in the routed JSON).
# Writes $RUNS/suite/KERNEL_SEED/{result.txt, draws.txt, exp.txt}; prints the result line.
set -uo pipefail
K=$1; S=$2; ND=${3:-4}; MAXIT=${4:-4}
export PNR_TIMEOUT=${PNR_TIMEOUT:-3600}   # build_bench.sh's per-seed limit (default 420 s): a loaded machine passed it
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/home/user/runs}; export RUNS
# SUITE_TAG=T (opt-in; unset, the names below are the ones they were): the loop's routes are T_K_S_<it> instead of
# su_K_S_<it> and the results go to $RUNS/suite/K_S_T, so a variant of the flow (e.g. BDC_MEM_FASTFALL=1 in the
# environment, which every bdc call here and in the builds reads) is judged beside the default on the same draws.
O=$RUNS/suite/${K}_$S${SUITE_TAG:+_$SUITE_TAG}; mkdir -p "$O"; : > "$O/draws.txt"
D=${K}_bench_gen
# verification data: the six original kernels use their gate vectors and oracles (with the bench's input masks);
# every other kernel reads kernels/K/vec.hex (Dynamatic's tests, which have no kernels/ directory -- one would shadow
# the test in bdc/frontend.sh: research/data/suite/vec/K.hex) and the generic oracle research/tools/suite/oracle.sh
case $K in
  xorshift) V=research/data/eventgraph/gate/xor19.hex; PV=research/data/fifteen/vec_xorshift.hex; OR="research/tools/fifteen/kernel_oracle.sh xorshift";;
  collatz) V=research/data/eventgraph/gate/col18.hex; PV=research/data/fifteen/vec_collatz.hex; OR="research/tools/fifteen/kernel_oracle.sh collatz";;
  collatz64) V=research/data/eventgraph/gate/c6419.hex; PV=research/data/fifteen/vec_c64_871.hex; OR="research/tools/fifteen/kernel_oracle.sh collatz64";;
  ipow) V=research/data/eventgraph/gate/ipow17.hex; PV=research/data/fifteen/vec_ipow.hex; OR="research/tools/fifteen/kernel_oracle.sh ipow";;
  # gcd / isprime: one long vector for P (their cost vectors run for hours in the decoded-netlist simulation); gcd's
  # draws on gcd8 (gcd18's edges and its longest pair; farm gcddraw1 timed out on 42 of 64 tasks with gcd18)
  isprime) V=research/data/alltable/isp17.hex; PV=research/data/suite/vec/isprime_period.hex; OR="research/tools/fifteen/kernel_oracle.sh isprime";;
  gcd) V=research/data/suite/vec/gcd8.hex; PV=research/data/suite/vec/gcd_period.hex; OR="research/data/gcd_draws/gcd_oracle.sh";;
  *) V=kernels/$K/vec.hex; [ -f "$R/$V" ] || V=research/data/suite/vec/$K.hex
     PV=kernels/$K/period.hex; [ -f "$R/$PV" ] || PV=research/data/suite/vec/${K}_period.hex; [ -f "$R/$PV" ] || PV=$V
     OR="research/tools/suite/oracle.sh $K";;
esac
# a v2 vector file (arrays; research/data/suite/bench/README.md) takes the memory oracle and the arrays' read-back
MEMV=0; head -1 "$R/$V" 2>/dev/null | grep -q '^// benchvec' && MEMV=1
fin() { echo "$K $S $*" | tee "$O/result.txt"; exit 0; }
# compiles at all? (the frontend fixture, then bdc with BDC_AUTO=1, as cells/hw/build_bench.sh runs them; a kernel the
# compiler refuses stays in the suite with the reason)
FX=$R/build/frontend/$K/comp/handshake_transformed.mlir
[ -f "$FX" ] || fin "status=DOES-NOT-COMPILE (frontend: no handshake fixture)"
# AUTO_PROVED_RW=1 (opt-in, 2026-11-20; research/data/autorw/): formal's proved loop-test passes on this kernel's
# handshake MLIR (FORMAL_DIR/formal/tools-A/rewrite/auto_rewrites.sh: plain_pass, then eq2_pass), matched by structure
# (no kernel names, no hashes), each kept only when Lean proves the rewritten graph equal to its input (token level,
# every schedule).  FORMAL_DIR = a claude/formal checkout whose modules Formal.Rewrite.PlainPass, .Steps.ScriptSound and
# .Rename are built (lake build), Lean on PATH (default $HOME/.elan/bin).  The import runs with BDC_RING_FUSE=0: the
# proof is about the graph before ring fusion, which bdc applies to the emitted graph afterwards (formal's passes
# refuse the fused import: "0 matches of the pattern").  Where a pass proves, every build of the loop reads the
# rewritten MLIR (lane2.sh MLIR_OVERRIDE) and the result line says rw=<passes>; elsewhere rw=none and the build is as
# before.  Unset: nothing here runs and the line is unchanged.
RW=""
if [ "${AUTO_PROVED_RW:-0}" = 1 ]; then
  FD=${FORMAL_DIR:?AUTO_PROVED_RW=1 needs FORMAL_DIR}
  mkdir -p "$R/build/autorw"; RWF=build/autorw/$K.mlir; rm -f "$R/$RWF"
  ( PATH=${LEAN_BIN:-$HOME/.elan/bin}:$PATH BDC_AUTO=1 BDC_RING_FUSE=0 \
      bash "$FD/formal/tools-A/rewrite/auto_rewrites.sh" "$FX" "$R/$RWF" --bdc "$R/bdc" ) > "$O/autorw.log" 2>&1
  pv=$(grep -oE '^(plain_pass|eq2_pass): PROVED' "$O/autorw.log" | cut -d: -f1 | paste -sd+)
  if [ -n "$pv" ] && [ -s "$R/$RWF" ] && ! cmp -s "$FX" "$R/$RWF"; then
    export MLIR_OVERRIDE=$RWF; FX=$R/$RWF; RW=" rw=$pv"
  else
    RW=" rw=none"
  fi
fi
CE=$O/compile; mkdir -p "$CE"
python3 "$R/bdc/auto.py" "$FX" "$CE/auto.mlir" > "$CE/log" 2>&1 && BDC_AUTO=1 python3 "$R/bdc/emit.py" "$CE/auto.mlir" --no-top \
  -o "$CE/kernel.v" >> "$CE/log" 2>&1 || fin "status=DOES-NOT-COMPILE (bdc: $(grep -E 'Error' "$CE/log" | tail -1 | cut -c1-140))"
[ -f "$R/$V" ] || fin "status=NO-VECTORS ($V)"
if [ "$MEMV" = 1 ]; then
  ( cd "$R" && ORACLE_RUNS=${GATE_NRUNS:-2} ORACLE_MEMOUT="$O/memexp.txt" research/tools/suite/oracle_mem.sh "$K" "$V" ) > "$O/exp.txt" 2> "$O/oracle.err" \
    || fin "status=NO-ORACLE ($(head -1 "$O/oracle.err"))"
  export GATE_MEMEXP="$O/memexp.txt"   # bench_gate.sh: every array read back after each call must equal the C's
else
  ( cd "$R" && $OR < "$V" ) > "$O/exp.txt" 2> "$O/oracle.err" || fin "status=NO-ORACLE ($(head -1 "$O/oracle.err"))"
  [ "$(grep -c . "$O/exp.txt")" = "$(grep -c . "$R/$V")" ] || fin "status=NO-ORACLE (line count)"
fi
N=${SUITE_TAG:-su}_${K}_$S
# SUITE_SKIP_AUTO=1 (opt-in): the sizing loop already ran elsewhere -- a farm task's auto/ files copied to $RUNS/auto/N
# (result.txt names the route it kept) and that route rebuilt here from its own sizes with lane2.sh under the same
# name (N_<it>, the same seed: nextpnr reproduces it byte for byte), its lane2 line in $RUNS/auto/N/it_<it>.txt.
# Everything below (the bits, the draws, the metrics) then runs as after a loop of its own.  For a farm task that ran
# out of time after its loop (farm suite8: gather s2, if_loop_2 s2, sumi3_mem, fir), or one resumed elsewhere.
[ "${SUITE_SKIP_AUTO:-0}" = 1 ] || \
"$R/research/tools/auto/auto_size.sh" "sl_${K}_$S" "$N" "$K" "$S" "$R/$PV" "$MAXIT" > "$O/auto.log" 2>&1
AR=$(tail -1 "$RUNS/auto/$N/result.txt" 2>/dev/null)
case $AR in
  CLEAN*) IT=$(echo "$AR" | grep -o 'it=[0-9]*' | cut -d= -f2); RULE=clean;;
  "NOT CLEAN after"*) IT=$(echo "$AR" | sed -n "s/^NOT CLEAN after \([0-9]*\).*/\1/p"); RULE=not-clean;;
  "NOT CLEAN it="*) IT=$(echo "$AR" | grep -o 'it=[0-9]*' | cut -d= -f2); RULE=not-clean-unfixable;;
  "BUILD FAILED it="*) BI=$(echo "$AR" | grep -o 'it=[0-9]*' | cut -d= -f2); BL=$RUNS/hw/${N}_$BI/build.log
    # a place-and-route that ran out of time is the machine, not the compiler (PNR_TIMEOUT, build_bench.sh)
    if grep -q "per-seed timeout" "$BL" 2>/dev/null; then fin "status=PNR-TIMEOUT (it=$BI; raise PNR_TIMEOUT or load less)"; fi
    # bdc already compiled it (the check at the top), so a failed build is synthesis / place and route / the harness
    fin "status=BUILD-FAILED (it=$BI: $( { grep -m1 -iE 'error|failed' "$BL" 2>/dev/null || tail -1 "$RUNS/auto/$N/it_$BI.log" 2>/dev/null; } | cut -c1-140))";;
  *) fin "status=FLOW-FAILED ($AR)";;
esac
# auto_size.sh AUTO_SHIP_LEAST=1: a NOT CLEAN loop may ship an earlier route than its last ("shipped it=X"); judge that one
SHIP=$(echo "$AR" | grep -o 'shipped it=[0-9]*' | head -1 | cut -d= -f2); [ -n "$SHIP" ] && IT=$SHIP
RT=${N}_$IT; HW=$RUNS/hw/$RT; RD=$RUNS/r/$RT
LINE=$(cat "$RUNS/auto/$N/it_$IT.txt" 2>/dev/null)
md5=$(echo "$LINE" | awk '{print $2}'); P=$(echo "$LINE" | grep -o 'P=[0-9A-Z]*' | cut -d= -f2)
eq=$(echo "$LINE" | grep -q 'NOT EQUIVALENT' && echo NOT-EQUIVALENT || (echo "$LINE" | grep -q 'EQUIVALENT' && echo EQUIVALENT || echo EQUIV?))
ff=$(echo "$LINE" | grep -q 'FFMUX-FLAG' && echo FFMUX-FLAG || echo ffmux-clean)
luts=$(python3 - "$HW/${D}_routed.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))["modules"]
n = sum(1 for t in m.values() for c, v in t.get("cells", {}).items() if v["type"] == "SLICE_LUTX" and "udut" in c)
print(n)
PY
)
lat=$(grep BENCHRES "$RD/run.log" 2>/dev/null | grep -o 'latmax=[0-9]*' | cut -d= -f2 | sort -n | tail -1)
# AUTO_TRIM=1 (auto_size.sh): the route judged below is the trimmed one; its untrimmed P and the trim count are added
# to the line (absent otherwise, so the default line is unchanged)
P0=$(grep -o 'P=[0-9A-Z]*' "$RUNS/auto/$N/it_${IT}_untrimmed.txt" 2>/dev/null | head -1 | cut -d= -f2)
TR=""; [ -n "$P0" ] && TR=" P_untrimmed=$P0 trims=$(cat "$RUNS/auto/$N/trim_$IT.txt" 2>/dev/null | grep -c .)"
base="P=${P:-NA}$TR lat_max_cyc=${lat:-NA} luts=$luts sdf=$md5 rule=$RULE it=$IT bits=$eq $ff$RW"
if [ "$eq" != EQUIVALENT ] || [ "$ff" != ffmux-clean ]; then fin "status=NOT-A-BOARD-ROUTE $base"; fi
# DRAW_JOBS draws at a time (default 1); each draw has its own work directory and draw file
# GATE_RUNTS=1 by default (report only: the verdict line gains a "runts" field, a pass stays a pass; subagent steerrunt,
# research/data/suite/steerrunt/README.md): every draw counts pulses under 150 / 500 / 1000 ps on the kernel's handshake
# outputs, at no measurable cost; GATE_RUNTS=fail makes such a pulse fail the draw, GATE_RUNTS= (empty) turns it off.
draw() { local k=$1 g
  g=$(GATE_RUNTS=${GATE_RUNTS-1} "$R/research/tools/eventgraph/bench_gate.sh" "$HW" "$D" "$RUNS/g/$RT/d$k" "$R/$V" "$O/exp.txt" "draw:$k" 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3-8 "$RUNS/g/$RT/d$k/draw_$k.txt" 2>/dev/null) :: ${g:-none}" > "$O/draw_$k.txt"
  grep '^BENCHRES' "$RUNS/g/$RT/d$k/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$O/benchres_$k.txt"
  rm -rf "$RUNS/g/$RT/d$k/draw_$k" 2>/dev/null; }
mkdir -p "$RUNS/g/$RT"; [ -f "$RD/xray.sdf" ] && for j in $(seq 1 "$ND"); do k=$((10000 + 100 * S + j)); mkdir -p "$RUNS/g/$RT/d$k"; cp "$RD/xray.sdf" "$RUNS/g/$RT/d$k/xray.sdf"; done
for j in $(seq 1 "$ND"); do
  draw $((10000 + 100 * S + j)) &
  while [ "$(jobs -rp | wc -l)" -ge "${DRAW_JOBS:-1}" ]; do sleep 5; done
done; wait
pass=0
for j in $(seq 1 "$ND"); do k=$((10000 + 100 * S + j)); cat "$O/draw_$k.txt" >> "$O/draws.txt"; grep -q ":: PASS " "$O/draw_$k.txt" && pass=$((pass + 1)); done
st=PASS; [ "$pass" = "$ND" ] || st=FAIL
# latency per call under the draws: per vector the median over draws of latmin (host cycles of 12 ns), then the median
# and the sum over the vectors
lat=$(python3 - "$O" <<'PY'
import glob, re, statistics as st, sys
per = {}
for f in glob.glob(sys.argv[1] + "/benchres_*.txt"):
    for l in open(f):
        d = dict(re.findall(r"(\w+)=(\S+)", l))
        if "batch" in d and "latmin" in d:
            per.setdefault(int(d["batch"]), []).append(int(d["latmin"]) * 12)
v = [st.median(x) for _, x in sorted(per.items())]
print("lat_call_med_ns=%d lat_call_sum_ns=%d nvec=%d" % (st.median(v), sum(v), len(v)) if v else "lat_call_med_ns=NA")
PY
)
fin "status=$st draws=$pass/$ND $base $lat"
