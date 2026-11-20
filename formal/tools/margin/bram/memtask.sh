#!/usr/bin/env bash
# margin/bram/memtask.sh K SEED SIZES|none SDF8|- OUT [NDRAWS] [K0]  (shard C, UNTRUSTED simulation): one route of a MEMORY
# kernel (research's benchvec vectors) judged by formal's simx on the circuit decoded from its own bitstream, RAMB18E1s
# included (margin/bram/).  Like tools-B/auto/suite/task.sh (shard B), whose steps it follows:
#   1. vectors (kernels/K/vec.hex, else research/data/suite/vec/K.hex; must be benchvec v2), oracle from the C
#      (research/tools/suite/oracle_mem.sh, ORACLE_RUNS=1: one run per call, results and final array contents);
#   2. the route: build_bench.sh in a copy of research's tree ($RS, a claude/research checkout), FLOW=auto (BDC_AUTO=1,
#      default) or FLOW=default, BD_SIZES=SIZES (none = bdc's estimates), NEXTPNR_SEED=SEED (PNR_SEED=N overrides: research's alt-seed finishes), BD_DSP=1 BD_NO_TIGHTEN=1
#      BD_SIZES_GATE=0; any BDC_* in the caller's environment is passed on; SDF8 = research's sdf md5 prefix to match
#      ('-' = a new route);
#   3. the bits read back (prjxray bit2fasm) and decoded: decode_bram.py (LUTs, routes, DSP48E1, RAMB18E1, every
#      DSP / RAM pin checked one-to-one against nextpnr's routed json), build_net.py (RC_TREE=1), dsp_gates.py,
#      bram_gates.py; the kernel boundary (margin/boundary_bench.py, mk_bnd_mem.py (A's mk_bnd_sim.py generalised), B's bnd_const.py);
#   4. memvec.py; NDRAWS (16) draws of research's model from K0 (10000 + 100 SEED + 1) and NDRAWS slow-carry draws
#      (CARRY4 / F7F8 / FF / RAMB18 in [0.8, 1.0]) with tools-B/auto/xdraws.py -> draws.py --mem.
# The host's fill: by default memvec writes the arrays into the RAMs between calls; HOSTPORT=1 drives each write through
# the array's host port instead, as the bench's sequencer does (simx --hostport; payload one aclk before the request, a
# 2-flop synchronised acknowledge, HOSTCLK 12000 ps). The read-back is always read from the RAM's contents.
# OUT/summary.txt.  Env: RS (default /home/user/rs), TREE (default $OUT/tree: a private copy of cells/ bdc/ build/frontend).
set -uo pipefail
K=$1; S=$2; Z=$3; [ "$Z" = none ] || Z=$(readlink -f "$Z"); M8=$4; O=$(mkdir -p "$5" && cd "$5" && pwd); ND=${6:-16}; K0=${7:-$((10000 + 100 * S + 1))}
H=$(cd "$(dirname "$0")" && pwd); M=$(cd "$H/.." && pwd); F=$(cd "$M/../.." && pwd); A=$F/tools-A/target; B=$F/tools-B/auto
RS=${RS:-/home/user/rs}; export TC=${TC:-$HOME/dev2/lib/fpgatoolchain} RC_TREE=1
SM=$O/summary.txt; : > "$SM"; say() { echo "$*" | tee -a "$SM"; }
source "$TC/openxc7/export.sh" > /dev/null
V=kernels/$K/vec.hex; [ -f "$RS/$V" ] || V=research/data/suite/vec/$K.hex
head -1 "$RS/$V" 2>/dev/null | grep -q '^// benchvec' || { say "$K $S SKIP (no benchvec vectors: use tools-B/auto/suite/task.sh)"; exit 0; }
mkdir -p "$O/v"
( cd "$RS" && ORACLE_RUNS=1 ORACLE_MEMOUT="$O/v/memexp.txt" research/tools/suite/oracle_mem.sh "$K" "$V" ) > "$O/v/exp.txt" 2> "$O/oracle.err" \
  || { say "$K $S NO-ORACLE $(head -1 "$O/oracle.err")"; exit 0; }
T=${TREE:-$O/tree}
if [ ! -d "$T/cells" ]; then mkdir -p "$T/build"; cp -r "$RS/cells" "$RS/bdc" "$T/"; cp -r "$RS/cloud/fixtures/frontend" "$T/build/"; fi
# FIXTURES=<dir under cloud/fixtures> (research's exit1: frontend_exitcond, made with BDC_FE_EXITCOND=1): its kernel MLIR
# replaces the default one, as the request does; always re-copied, so a reused tree never keeps another flow's MLIR
cp "$RS/cloud/fixtures/${FIXTURES:-frontend}/$K/comp/"*.mlir "$T/build/frontend/$K/comp/" \
  || { say "$K $S NO FIXTURE ${FIXTURES:-frontend}/$K"; exit 0; }
FL=(); [ "${FLOW:-auto}" = auto ] && FL=(BDC_AUTO=1)
# REUSE=1: keep a build already in the tree (same K) and only redo the decode and draws
[ "${REUSE:-0}" = 1 ] && [ -f "$T/cells/build/hw/${K}_bench_gen/${K}_bench_gen.bit" ] || \
( cd "$T/cells" && rm -rf "build/hw/${K}_bench_gen" && env "${FL[@]}" NEXTPNR_SEED=${PNR_SEED:-$S} BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 \
    BD_SIZES="$Z" PNR_TIMEOUT=${PNR_TIMEOUT:-3600} ./hw/build_bench.sh "$K" ) > "$O/build.log" 2>&1 \
  || { say "$K $S BUILD FAILED: $(grep -m1 -iE 'error|fail' "$O/build.log" | cut -c1-120)"; exit 0; }
BD=$T/cells/build/hw/${K}_bench_gen; N=${K}_bench_gen
md=$(md5sum "$BD/$N.sdf" | cut -c1-8)
say "$K $S flow ${FLOW:-auto}${FIXTURES:+ fixtures $FIXTURES} sizes $(basename "$Z") sdf $md (research $M8) $([ "$md" = "$M8" ] && echo SAME || echo DIFFERENT) nextpnr $(sha256sum "$TC/openxc7/bin/nextpnr-xilinx" | cut -c1-16)"
[ "$md" = "$M8" ] || [ "$M8" = - ] || exit 0
W=$O/w; mkdir -p "$W/m"; PRJ=$TC/openxc7-src/prjxray; DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7
PYTHONPATH="$PRJ:$PRJ/third_party/fasm:$TC/openxc7/lib/python" python3 -W ignore "$PRJ/utils/bit2fasm.py" --db-root "$DB" \
  --part xc7z010clg400-1 --bitread "$TC/openxc7/bin/bitread" "$BD/$N.bit" > "$W/raw.fasm" 2> "$O/bit2fasm.log"
if [ -s "$W/raw.fasm" ]; then python3 "$B/fasm_bits.py" "$W/raw.fasm" "$W/m/fromBit.fasm" > /dev/null; SRC=bits
else cp "$BD/$N.fasm" "$W/m/fromBit.fasm"; SRC="nextpnr FASM (bit2fasm failed)"; fi; rm -f "$W/raw.fasm"
cp "$BD/$N.json" "$W/m/synth.json"; cp "$BD/${N}_routed.json" "$W/m/routed.json"
cp "$T/cells/build/gen/$N.v" "$T/cells/build/gen/${K}_kernel_bench.v" "$W/"
say "decoded from $SRC; bits md5 $(md5sum < "$BD/$N.bit" | cut -c1-8)"
( cd "$W/m" && : > empty.xdc &&
  python3 "$H/decode_bram.py" fromBit.fasm empty.xdc --json d0.json --routed routed.json 2>&1 | grep -E '^decode_(bram|dsp):' &&
  python3 "$A/build_net.py" d0.json fromBit.fasm - net0.json > /dev/null 2> build_net.err &&
  { if grep -q '"dsp48e1"' d0.json; then python3 "$M/dsp/dsp_gates.py" d0.json net0.json net1.json --routed routed.json --check 500 2>&1 | tail -1;
    else cp net0.json net1.json; fi; } &&
  python3 "$H/bram_gates.py" d0.json net1.json net.json &&
  python3 "$M/boundary_bench.py" synth.json routed.json net.json "$W/${K}_kernel_bench.v" "$W/$N.v" bnd_bench.json | tail -1 &&
  python3 "$H/mk_bnd_mem.py" bnd_bench.json bnd.json && python3 "$B/bnd_const.py" bnd.json net.json && rm -f net0.json net1.json
) > "$O/decode.out" 2>&1
[ -f "$W/m/bnd.json" ] || { say "DECODE FAILED: $(tail -2 "$O/decode.out" | tr '\n' ' ' | cut -c1-200)"; exit 0; }
grep -E "RAMB18 sites agree|DSP sites agree|ram gates|mismatches|operands" "$O/decode.out" | tee -a "$SM"
python3 "$H/memvec.py" "$RS/$V" "$O/v/exp.txt" "$O/v/memexp.txt" "$W/m/net.json" "$W/${K}_kernel_bench.v" "$O/v" 2>&1 | tee -a "$SM"
[ -s "$O/v/mem.txt" ] || { say "MEMVEC FAILED"; exit 0; }
for x in "" 0.8,1.0; do
  k0=$K0; [ -n "$x" ] && k0=$((K0 + 50))
  DRAW_XBAND=$x python3 "$B/xdraws.py" "$O/v/exp_num.txt" "$W/m/net.json" "$W/m/bnd.json" "$O/d$k0" --kernel "$K" --pairs $(cat "$O/v/pairs.txt") \
    --draws "$ND" --seed0 "$k0" --jobs "${JOBS:-4}" --routed "$W/m/routed.json" --tmax "${TMAX:-1900000000}" --mem "$O/v/mem.txt" ${HOSTPORT:+--hostport} > "$O/d$k0.log" 2>&1
  say "draws K $k0..$((k0 + ND - 1))${x:+ slow-carry/RAM $x}: $(grep '^draws [0-9]' "$O/d$k0.log" | head -1) $(grep -E 'seed [0-9]+ (FAIL|UND)' "$O/d$k0.log" | head -4 | tr '\n' ' ' | cut -c1-400)"
  cp "$O/d$k0/draws_summary.txt" "$O/draws_summary_$k0.txt" 2>/dev/null; cp "$O/d$k0/draws.txt" "$O/draws_$k0.txt" 2>/dev/null
  rm -rf "$O/d$k0/net.simx" "$O/d$k0/simx"
done
# hostrace (static host-write race, mid band): every RAM's slack, skew.py-guarded and -400 ps forms; the minimum of each
# beside the draws' minimum RAM setup margin (research's C64 question: which guard form the draws support)
if [ -n "${HOSTPORT:-}" ]; then
  timeout 1800 python3 "$H/hostrace.py" "$O" > "$O/hostrace.txt" 2>&1
  dm=$(cat "$O"/draws_1*.txt 2>/dev/null | grep -oE '(ADDR|WE|DI) setup -?[0-9]+' | awk '{print $3}' | sort -n | head -1)
  say "hostrace: $(grep -c 'CLKARDCLK earliest' "$O/hostrace.txt") RAMs; min slack $(grep -oE 'slack [-+][0-9]+' "$O/hostrace.txt" | awk '{print $2+0}' | sort -n | head -1) ps, guarded x0.772/x1.155 $(grep -oE 'x1.155 [-+][0-9]+' "$O/hostrace.txt" | awk '{print $2+0}' | sort -n | head -1) ps, -400 $(grep -oE ', -400 [-+][0-9]+' "$O/hostrace.txt" | awk '{print $3+0}' | sort -n | head -1) ps; draws' min RAM setup margin ${dm:-?} ps"
fi
