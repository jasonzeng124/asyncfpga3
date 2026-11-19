#!/usr/bin/env bash
# bench_gate.sh HWDIR DESIGN WORK VECFILE EXPFILE COL -- one full-stack correctness run of a bench route at one corner:
#   COL = max (SLOW_MAX) | min (FAST_MIN) | worst (delay chains 0.21, CARRY4/F7F8/FF and the RAMB18E1 1, rest 0.288, + M scatter:
#   region 0.02, wire 0.126, the measured residual -- JOURNAL 2026-11-04 00:24 / 2026-11-05 00:09)
#   | draw:K (one draw of the parametric delay model, see the case below; JOURNAL 2026-11-16).
# Netlist decoded from the .bit (fasm_equiv verdict), prjxray SDF, fid, ps7_bench.v FIXED mode, +FCLK_PS=12000
# (83.3 MHz), 2 runs per vector.  Verdict: every batch completed 2/2, its runs agreed (mism_st bit 0 clear; added
# 2026-11-16) and odata == EXPFILE line (derived from the C).
# v2 vector files (research/data/suite/bench/README.md: more operand words, arrays behind the host port): a batch
# also FAILS if filling its arrays failed (a BENCHMEM ... FILL FAILED line) or, with +MEMCHECK=1 in GATE_PLUSARGS,
# if any word read back differs.  GATE_MEMEXP=FILE (research/tools/suite/oracle_mem.sh's ORACLE_MEMOUT, the C's final
# array contents per call) adds +MEMDUMP=1 and FAILS a batch whose arrays, read back after it, differ.  GATE_NRUNS
# (default 2) is the runs per batch: a kernel that writes its arrays sees its own writes on the next run, so its
# oracle must be run with the same count (ORACLE_RUNS).
# A `void` line in EXPFILE (oracle_mem.sh: the kernel returns nothing; gen_bench.py completes its call on its control
# results and ODATA reads 0) has no result to compare: that call passes only on its arrays, so only with GATE_MEMEXP.
# Since 2026-11-18 (research/data/suite/ifloop.md): a batch whose SIG (the fold of every run's result) has an x is not a
# pass, and any `RAMB18 ` line in the run (the GLS RAM model's setup / hold violation, or a RAM clock that went x) fails
# the whole run; a clean run's verdict line is unchanged.
# GATE_RUNTS=1 | fail (opt-in, 2026-11-19; unset: the run and the verdict line are byte-identical to before): compile
# cells/gls/ps/gen_runt_mon.py's monitor into the run (build_ps.sh PS_RUNTS=1) and count, on every kernel steer / mux /
# merge / C-element / link enable output (at its driver in the bits-decoded netlist), every pulse narrower than three
# thresholds (GATE_RUNTS_T, default 150,500,1000 ps; a third threshold of 0 = the loop threshold, the run's longest
# kernel C-element loop + WIN/2 + 3 sigma: the widest pulse the gate's runt model can still reject).  The verdict line
# gets a "runts" field (counts, narrowest pulse of any width, longest kernel loop, the nets hit) and runts.txt (per net)
# is written beside run.log.  With GATE_RUNTS=fail a pulse narrower than the LAST threshold on a net of a class in
# GATE_RUNTS_CLASSES (default: every class) fails the run.  Why: the gate's runt model rejects a pulse shorter than the
# receiving C-element's loop, so a select race that fires on every call can pass (research/data/suite/hangs.md section
# 3, research/data/suite/steerrunt/README.md); whether silicon rejects such a pulse is BOARD-QUEUE item 2 (H_RUNT).
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
         export GLS_SDF_FIELD=band GLS_SDF_BAND=0.288 GLS_SDF_BAND_CELL=CARRY4=1,SELMUX2_1=1,SLICE_FFX=1,RAMB18E1_RAMB18E1=1 \
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
         export GLS_SDF_FIELD=band GLS_SDF_BAND=$XR GLS_SDF_BAND_CELL=CARRY4=$XK,SELMUX2_1=$XK,SLICE_FFX=$XK,RAMB18E1_RAMB18E1=$XK \
                GLS_SDF_BAND_INST=@$W/chains_$K.band GLS_SCATTER_REGION=0.02 GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=$K;;
  *) echo "COL?"; exit 2;;
esac
# one compile at a time on the machine: build_ps.sh's iverilog peaks at several GB (OOM kills lose runs)
CD=${COL/:/_}
if [ -n "${GATE_RUNTS:-}" ]; then
  export PS_RUNTS=1; IFS=, read -r RT1 RT2 RT3 <<< "${GATE_RUNTS_T:-150,500,1000}"
fi
"$R/research/tools/compile_slot.sh" "$G/ps/build_ps.sh" "$HW" "$W/$CD" "" bit > "$W/$CD.build.log" 2>&1
cd "$W/$CD"
# GATE_ANNOTATE=1: also run gate.vvp (cells/gls/build.sh: the SDF through iverilog's annotator, which names every arc it
# cannot place) -- it must print ANNOTATE_DONE with no SDF warning or error (CLAUDE.md); the verdict line says which.
ANN=""
if [ "${GATE_ANNOTATE:-0}" = 1 ]; then
  vvp gate.vvp > annotate.log 2>&1 || true
  ANN=" | annotate $(grep -q ANNOTATE_DONE annotate.log && echo DONE || echo MISSING) sdf-warn/err $(grep -ciE 'SDF (WARNING|ERROR)' annotate.log || true)"
fi
rm -f gate.vvp
vvp run_baked.vvp +FCLK_PS=12000 +MODE=1 +NRUNS=${GATE_NRUNS:-2} +VECFILE="$VEC" ${GATE_MEMEXP:+"+MEMDUMP=1"} +TBATCH=${GATE_TBATCH:-1200000} +TEND=20000000 ${GATE_PLUSARGS:-} ${GATE_RUNTS:+"+RUNT_T1=$RT1" "+RUNT_T2=$RT2" "+RUNT_T3=$RT3"} > run.log 2>&1 || true   # GATE_PLUSARGS: e.g. +META_INIT=0; GATE_TBATCH: ns per batch before HANG (default 1200000; preload runs, research/tools/preload)
rm -f run_baked.vvp
python3 - "$EXP" run.log "$(grep -o 'VERDICT: [A-Z_ ]*' fid/equiv.txt | head -1)" "${GATE_MEMEXP:-}" "$ANN" \
    ${GATE_RUNTS:+"$GATE_RUNTS" "${GATE_RUNTS_CLASSES:-}"} <<'PY'
import sys, re
exp = open(sys.argv[1]).read().split(); got = {}
memexp = {}
if sys.argv[4]:   # the C's final array contents per call (oracle_mem.sh ORACLE_MEMOUT)
    for l in open(sys.argv[4]):
        d = dict(re.findall(r"(\w+)=(\S+)", l)); memexp[(int(d["call"]), int(d["mem"]))] = d["data"]
memgot, membad = {}, set()
mon, onehot_fail = [], 0
ramev = 0
for l in open(sys.argv[2]):
    if l.startswith("BENCHRES"):
        d = dict(re.findall(r"(\w+)=(\S+)", l)); got[int(d["batch"])] = d
    elif l.startswith("BENCHMEMCHK"):
        d = dict(re.findall(r"(\w+)=(\S+)", l))
        if int(d["bad"]): membad.add(int(d["batch"]))
    elif l.startswith("BENCHMEM ") and "FILL FAILED" in l:
        membad.add(int(re.search(r"batch=(\d+)", l).group(1)))
    elif l.startswith("BENCHMEM "):
        d = dict(re.findall(r"(\w+)=(\S+)", l)); memgot[(int(d["batch"]), int(d["mem"]))] = d["data"]
    elif l.startswith("MEMPORTMON"):   # cells/gls/ps/gen_memport_mon.py (PS_MON_GEN): the ports' one-hot check
        d = dict(re.findall(r"(\w+)=(\S+)", l)); mon.append(d)
        if int(d["overlaps"]): membad.add(int(d["batch"]))
    elif l.startswith("MEMPORT ONEHOT FAIL"):
        onehot_fail += 1
    elif l.startswith("RAMB18 "):      # the GLS RAM model (cells/gls/prims.v): a setup / hold violation, or a clock that
        ramev += 1                     # went x ("treated as a possible edge"); either poisons what that edge did
for (j, m), v in memexp.items():
    if memgot.get((j, m)) != v: membad.add(j)
for j in membad: got.pop(j, None)   # a batch whose arrays were not what the C had is not a pass
# mism_st bit 0 = the bench's FIXED-mode repeatability latch: the batch's runs did not all return the same value. odata is
# the LAST run's result only, so a wrong first run followed by a right one passed this gate until 2026-11-16 (farm
# steerneg: 5 such runs judged PASS). A batch counts only if every run agreed AND the last one equals the oracle.
mm = [j for j in got if int(got[j].get("mism_st", "0"), 16) & 1]
# SIG folds EVERY run's result; an x / z in it means some run of the batch returned an unknown value, which the
# repeatability latch cannot see (its `!=` against an x reference is never true) and odata (the last run) hides
# (if_loop_1 seed 1, route sizes_7 + UMEM0_USETUP 3: run 0 of batch 0 read x through an x pulse on the RAM clock,
# run 1 was right, and this gate said PASS; research/data/suite/ifloop.md).  Such a batch is not a pass.
xr = [j for j in got if re.search(r"[xXzZ]", got[j].get("sig", ""))]
if onehot_fail: got.clear()   # two slots of one port at once: no batch of this run is a pass
# `void` (oracle_mem.sh, a kernel that returns nothing): no out0; the bench's ODATA is its constant 0 and the answer is
# the arrays, so such a call passes only if GATE_MEMEXP held this call's arrays and they matched (membad above).
def right(j, e):
    if e == "void":
        return got[j]["odata"] == "00000000" and any(c == j for c, _ in memexp)
    return got[j]["odata"] == e
ok = sum(1 for j, e in enumerate(exp) if j in got and right(j, e) and got[j]["completed"] == got[j]["n"]
         and j not in mm and j not in xr)
if ramev: ok = 0     # the RAM saw an edge it could not resolve: no batch of this run is a pass
cyc = sum(int(got[j]["cycles"]) for j in got)
nvoid = sum(1 for e in exp if e == "void")
if nvoid:
    sys.argv[5] = (" | void: arrays only" if memexp else " | void kernel WITHOUT GATE_MEMEXP: nothing checked, no pass") \
        + sys.argv[5]
# an EXPFILE with no line (an oracle that failed, a truncated file) is a run with nothing to compare: never a pass
passed = bool(exp and ok == len(exp))
if len(sys.argv) > 6:   # GATE_RUNTS (cells/gls/ps/gen_runt_mon.py): narrow pulses on the kernel's handshake outputs
    rsum, rnet, rcls = None, {}, {}
    for l in open(sys.argv[2]):
        if l.startswith("RUNTSUM ") and "minall=" in l:
            rsum = dict(re.findall(r"(\w+)=(\S+)", l))
        elif l.startswith("RUNTCLS "):   # (a line cut short by a killed run is skipped)
            d = dict(re.findall(r"(\w+)=(\S+)", l))
            if "minall" in d: rcls[d["cls"]] = d
        elif l.startswith("RUNTMON batch="):
            d = dict(re.findall(r"(\w+)=(\S+)", l))
            if "net" in d: rnet[int(d["k"])] = d   # cumulative: a net's last line wins
    fcls = [c for c in sys.argv[7].split(",") if c] if len(sys.argv) > 7 else []
    if rsum is None:
        sys.argv[5] += " | runts: NO MONITOR OUTPUT"
        if sys.argv[6] == "fail": passed = False
    else:
        hits = sorted(rnet.values(), key=lambda d: -(int(d["n3"]) + int(d["x"])))
        bad = [d for d in hits if (not fcls or d["cls"] in fcls) and int(d["n3"]) + int(d["x"]) > 0]
        top = ", ".join("%s %s.%s %s%s (%s ps)" % (d["cls"], d["inst"], d["role"], d["n3"],
                        ("+%sx" % d["x"]) if int(d["x"]) else "", d["min"]) for d in hits[:4])
        cl = " ".join("%s %s/%s" % (c, d["hit"], d["nets"]) for c, d in sorted(rcls.items()) if int(d["hit"]))
        sys.argv[5] += " | runts <%s/%s/%s ps %s/%s/%s x %s on %s of %s nets%s, narrowest %s ps, loops <= %s ps%s%s" % (
            rsum["t1"], rsum["t2"], rsum["t3"], rsum["n1"], rsum["n2"], rsum["n3"], rsum["x"], rsum["hit"], rsum["nets"],
            " (%s)" % cl if cl else "", rsum["minall"], rsum.get("tloopmax", "?"),
            (": " + top + (" ..." if len(hits) > 4 else "")) if hits else "",
            (" RUNTS FAIL (%d net(s)%s)" % (len(bad), " of " + "/".join(fcls) if fcls else "")) if sys.argv[6] == "fail" and bad else "")
        if sys.argv[6] == "fail" and bad: passed = False
        with open("runts.txt", "w") as f:
            f.write("# k cls inst role net n<%s n<%s n<%s hi lo x min_any_width_ps first_ps (cumulative, batch %s)\n"
                    % (rsum["t1"], rsum["t2"], rsum["t3"], rsum["batch"]))
            for d in hits:
                f.write(" ".join(d[c] for c in ("k", "cls", "inst", "role", "net", "n1", "n2", "n3", "hi", "lo", "x", "min",
                                                 "first")) + "\n")
            for c, d in sorted(rcls.items()):   # per class: the narrowest pulse of ANY width (handshakes included)
                f.write("# class %s nets %s hit %s pulses<%s %s narrowest_any %s\n" % (c, d["nets"], d["hit"], rsum["t3"],
                                                                                  d["n3"], d["minall"]))
print("%s %d/%d cycles %d %s%s%s" % ("PASS" if passed else "FAIL", ok, len(exp), cyc, sys.argv[3],
      (" | MISMATCH in batch(es) %s" % ",".join(map(str, sorted(mm)))) if mm else "",
      (" | MEMORY wrong in batch(es) %s" % ",".join(map(str, sorted(membad)))) if membad else "") + sys.argv[5]
      + ((" | X in a run's result (SIG) in batch(es) %s" % ",".join(map(str, sorted(xr)))) if xr else "")
      + ((" | RAMB18 timing events %d" % ramev) if ramev else "")
      + ((" | memport one-hot: %d batch line(s), host reqs %d, kernel reqs %d, overlaps %d%s" % (
          len(mon), sum(int(d["host_reqs"]) for d in mon), sum(int(d["kernel_reqs"]) for d in mon),
          sum(int(d["overlaps"]) for d in mon), " ONEHOT FAIL" if onehot_fail else "")) if mon or onehot_fail else ""))
PY
