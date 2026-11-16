#!/usr/bin/env bash
# eval_task.sh NAME KERNEL SIZES_VH SEED VEC GATE_HEX GATE_EXP [ENV...] -- one route, every check, for the farm
# (research/cluster/README.md) or locally.  Writes a summary to ${OUT:-.}/eval.txt:
#   1. the bench build + itercost stack + event graph (lane2.sh; MLIR_OVERRIDE honoured): period, odata, fasm_equiv, ffmux
#   2. the static check of the owner's full-range rule (JOURNAL 2026-11-14): corner_audit at NOMINAL (--uniform 0.288)
#      (the line also lists every rule H / I / F / K / L / B / C row below 0: "hold/close")
#      and WORST, measured-residual guards, on this route as built; every kernel rule A / A' / E constraint below 0
#      (tighten's unsized bundled-channel row "a" is listed apart)
#   3. the full gate: bench_gate.sh SLOW_MAX / FAST_MIN / worst+M with the C-derived oracle.
#   (SPEC_CASES=inst:k) the static check per case, LONG / SHORT, and the in-cell select race (spec_select.py).
#   4. (HOLD_VEC=vector file) the trace-measured hold check at FAST_MIN (hold_trace.py) -> hold.tsv, and per latch bit
#      with the close at each bit's enable pin (hold_bits.py) -> hold_bits.tsv.
#   LINE_ACCT=1 (with TSE_VEC): research/tools/itercost/line_account.py at worst and nominal -> la_*/lines.{tsv,md}.
#   STATIC_ONLY=1: the build and step 2 only (no gate, hold or TSE); TSE_ONLY=1: the build and step 5 only.
#   5. (TSE_VEC=vector file with a long steady loop, e.g. vec_xorshift.hex) rule H with C-element semantics and token
#      counts (research/tools/eventgraph/tsehold.py): a DUMP_FIELD=min run's event graph against a FAST_MIN SDF, and
#      the build's own (worst-column) graph against corner_audit's worst SDF -> tse_min.txt, tse_worst.txt.
# Steps 2 and 3 run in parallel (5 processes; memory ~3 x 2.4 GB for the gate sims).
set -uo pipefail
N=$1; K=$2; Z=$3; S=$4; VEC=$5; GH=$6; GE=$7; shift 7
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/home/user/runs}; export RUNS
O=${OUT:-$PWD}; mkdir -p "$O"; E=$O/eval.txt; : > "$E"
L=$R/research/tools/fifteen/lane2.sh
line=$("$L" "e$S" "$N" "$K" "$Z" "$S" "$VEC" "$@" 2>&1 | tail -1)
echo "build $line" >> "$E"
grep -o 'latmin=[0-9]*' "$RUNS/r/$N/run.log" 2>/dev/null | head -1 | sed 's/^/latency /' >> "$E"   # cycles of 12 ns, the itercost vector
HW=$RUNS/hw/$N; RD=$RUNS/r/$N
cp "$RD/fid/equiv.txt" "$O/equiv.txt" 2>/dev/null   # fasm_equiv: which kinds made a NOT EQUIVALENT (2026-11-15)
[ -f "$HW/${K}_bench_gen.sdf" ] || { echo "RESULT build-failed" >> "$E"; tail -20 "$HW/build.log" > "$O/build_tail.txt" 2>/dev/null; exit 1; }
CA=$RUNS/ca/$N; mkdir -p "$CA/seed1/pnr"
ln -sf "$RD/xray.sdf" "$CA/seed1/pnr/soak_xray.sdf"; ln -sf "$HW/${K}_bench_gen_routed.json" "$CA/seed1/pnr/soak_routed.json"
cp "$R/$Z" "$CA/seed1/pnr/sizes.vh"
cp "$R/${MLIR_OVERRIDE:-build/frontend/$K/comp/handshake_transformed.mlir}" "$CA/input.mlir"
if [ -z "${TSE_ONLY:-}" ]; then
# CA_EXTRA: extra corner_audit flags for step 2 (e.g. --shrink-selects: mux delays and select links proposed by rules M / E)
python3 "$R/research/tools/corner_audit.py" "$CA/seed1" --prefix bridge_i.udut. ${CA_EXTRA:-} --out "$CA/worst" > "$CA/worst.log" 2>&1 &
python3 "$R/research/tools/corner_audit.py" "$CA/seed1" --prefix bridge_i.udut. ${CA_EXTRA:-} --uniform 0.288 --out "$CA/nom" > "$CA/nom.log" 2>&1 &
fi
if [ -n "${SPEC_CASES:-}" ]; then   # BDC_SPEC_INC cells: the static check per case (LONG / SHORT), corner_audit --drop-inst/--cut
  for sc in ${SPEC_CASES//,/ }; do
    si=${sc%%:*}; sk=${sc##*:}; s0=$(( (sk + 3) / 4 ))          # first CARRY4 slice the carry cannot reach when abort = 0
    SA="$si\\.\\\$abc\\S* -> \\S*$si\\.uspec/"; SC="^\\S*$si\\.\\S*slice\\[([$s0-9]|[1-9][0-9])\\]\\.genblk1\\.carry4/"
    for m in nom worst; do X=""; [ $m = nom ] && X="--uniform 0.288"
      python3 "$R/research/tools/corner_audit.py" "$CA/seed1" --prefix bridge_i.udut. $X --drop-inst "$si\\.udly_s\\." --cut "$SA" --no-size --out "$CA/${si}_long_$m" > "$CA/${si}_long_$m.log" 2>&1 &
      python3 "$R/research/tools/corner_audit.py" "$CA/seed1" --prefix bridge_i.udut. $X --drop-inst "$si\\.udly\\.chain" --cut "$SC" --cut "$SA" --no-size --out "$CA/${si}_short_$m" > "$CA/${si}_short_$m.log" 2>&1 &
    done
  done
fi
# step 5's graph: one period per marker interval, else two (routes whose iterations alternate, 2026-11-15)
tse_graph() { mkdir -p "$(dirname "$2")"; for st in 1 2; do
    python3 "$R/research/tools/eventgraph/eventgraph.py" "$1" auto --rj "$HW/${K}_bench_gen_routed.json" --stride $st --out "$2" > "$2.log" 2>&1
    [ -f "$2/nodes.tsv" ] && grep -q "CHECK period equal: PASS" "$2/check.txt" 2>/dev/null && return 0; rm -rf "$2"; done; return 1; }
G=$RUNS/g/$N
if [ -z "${TSE_ONLY:-}" ] && [ -z "${STATIC_ONLY:-}" ]; then
for C in max min worst; do
  ( r=$("$R/research/tools/eventgraph/bench_gate.sh" "$HW" "${K}_bench_gen" "$G/$C" "$R/$GH" "$R/$GE" "$C" 2>&1 | tail -1)
    echo "gate $C $r" > "$O/gate_$C.txt" ) &
done
fi   # TSE_ONLY
if [ -n "${HOLD_VEC:-}" ] && [ -z "${TSE_ONLY:-}" ] && [ -z "${STATIC_ONLY:-}" ]; then   # trace-measured hold at every link / pipe input stage, FAST_MIN (hold_trace.py)
  ( DUMP_FIELD=min "$R/research/tools/eventgraph/fullstack_dump.sh" "$HW" "${K}_bench_gen" "$RUNS/hold/$N" "$R/$HOLD_VEC" > "$RUNS/hold_$N.log" 2>&1
    python3 "$R/research/tools/fifteen/hold_trace.py" "$RUNS/hold/$N" "$HW/${K}_kernel_bench.v" > "$O/hold.tsv" 2>&1
    python3 "$R/research/tools/fifteen/hold_bits.py" "$RUNS/hold/$N" "$HW/${K}_kernel_bench.v" > "$O/hold_bits.tsv" 2>/dev/null
    rm -f "$RUNS/hold/$N/dump.vcd" ) &
fi
if [ -n "${TSE_VEC:-}" ]; then   # step 5's FAST_MIN run (the worst graph is lane2's own, already built)
  ( DUMP_FIELD=min "$R/research/tools/eventgraph/fullstack_dump.sh" "$HW" "${K}_bench_gen" "$RUNS/tmin/$N" "$R/$TSE_VEC" > "$RUNS/tmin_$N.log" 2>&1
    tse_graph "$RUNS/tmin/$N" "$RUNS/gtmin/$N"
    rm -f "$RUNS/tmin/$N/dump.vcd" "$RUNS/tmin/$N/netlist_baked.v" ) &
  if [ ! -f "$RD/eventgraph/nodes.tsv" ]; then   # lane2's own graph failed (alternating period): rerun the worst dump
    ( "$R/research/tools/eventgraph/fullstack_dump.sh" "$HW" "${K}_bench_gen" "$RUNS/tworst/$N" "$R/$TSE_VEC" > "$RUNS/tworst_$N.log" 2>&1
      tse_graph "$RUNS/tworst/$N" "$RUNS/gtworst/$N"
      rm -f "$RUNS/tworst/$N/dump.vcd" "$RUNS/tworst/$N/netlist_baked.v" ) &
  fi
fi
wait
if [ -n "${TSE_VEC:-}" ]; then
  mkdir -p "$CA/tmin"; ln -sf "$HW/${K}_bench_gen_routed.json" "$CA/tmin/soak_routed.json"
  python3 "$R/research/tools/corner_sdf.py" "$RD/xray.sdf" "$CA/tmin/soak_routed.json" "$CA/tmin/soak.sdf" --band 0 > /dev/null 2>&1
  mkdir -p "$CA/tworst"; ln -sf "$HW/${K}_bench_gen_routed.json" "$CA/tworst/soak_routed.json"   # the full stack's worst column
  python3 "$R/research/tools/corner_sdf.py" "$RD/xray.sdf" "$CA/tworst/soak_routed.json" "$CA/tworst/soak.sdf" --band 0.288 \
      --cell CARRY4=1,SELMUX2_1=1,SLICE_FFX=1 --inst-rx '\.chain\.g\[\d+\]\.u$:0.21' > /dev/null 2>&1
  GW=$RD/eventgraph; [ -f "$GW/nodes.tsv" ] || GW=$RUNS/gtworst/$N
  python3 "$R/research/tools/eventgraph/tsehold.py" "$RUNS/gtmin/$N" "$CA/tmin/soak.sdf" > "$O/tse_min.txt" 2>&1
  python3 "$R/research/tools/eventgraph/tsehold.py" "$GW" "$CA/tworst/soak.sdf" > "$O/tse_worst.txt" 2>&1
  for c in min worst; do
    if ! grep -q "self-check" "$O/tse_$c.txt"; then echo "tse $c ERROR (no graph or tsehold failed; tse_$c.txt)" >> "$E"; continue; fi
    rows=$(awk '$4 ~ /^-[0-9]+$/ {print $4, $1}' "$O/tse_$c.txt" | sed 's/^/TSE /' | tr '\n' ';')
    unc=$(awk '/NOT COVERED/ && $3 ~ /^-[0-9]+$/ {print $3, $1}' "$O/tse_$c.txt" | tr '\n' ';')
    echo "tse $c ${rows:-CLEAN} | not covered, OR < 0: ${unc:-none} | $(grep -o 'self-check.*' "$O/tse_$c.txt" | cut -c1-80)" >> "$E"
    cp "$([ $c = min ] && echo "$RUNS/gtmin/$N" || echo "$GW")/check.txt" "$O/tse_graph_check_$c.txt" 2>/dev/null
  done
fi
if [ -n "${LINE_ACCT:-}" ]; then   # PROGRAM "second lead": every delay line on the loop (needs TSE_VEC for the graph)
  GW=$RD/eventgraph; [ -f "$GW/nodes.tsv" ] || GW=$RUNS/gtworst/$N
  for c in worst nom; do
    python3 "$R/research/tools/itercost/line_account.py" "$CA/$c" --graph "$GW" --out "$O/la_$c" > "$O/la_$c.log" 2>&1 \
      || echo "line_account $c ERROR (la_$c.log)" >> "$E"
    rm -f "$O/la_$c/paths.txt"   # arc-by-arc paths are large; the tables keep the split
  done
fi
[ -n "${TSE_ONLY:-}" ] || for c in nom worst; do
  f=$CA/$c/report.txt
  if [ -f "$f" ]; then
    # rule E rows carry the cell type in field 3 (E -255 bd_mux <inst> ...): until 2026-11-15 this line read field 3
    # only, so no E row on a mux or steer ever reached it (JOURNAL 2026-11-15, correction).
    neg=$(awk '$1~/^(A|E)$/ && $2+0<0 && ($3~/udut/ || $4~/udut/) {print $1, $2, ($3~/udut/ ? $3 : $4)}' "$f" | sort -u | sed 's/bridge_i.udut.//' | tr '\n' ';')
    a=$(awk '$1=="a" && $2+0<0 && $3~/udut/ {print $2, $3}' "$f" | sort -u | sed 's/bridge_i.udut.//' | tr '\n' ';')
    # every other rule corner_audit sizes (SIZED_RULES less A / E; D is a screen, J has no line): H (hold), I (capture),
    # F (fast-fall flush), K, L, B, C.  Until 2026-11-15 this line showed A / E only and the H / I rows were never read.
    hi=$(awk '$1~/^[FHIKLBC]$/ && $2+0<0 && $3~/udut/ {print $1, $2, $3}' "$f" | sort -u | sed 's/bridge_i.udut.//' | tr '\n' ';')
    echo "static $c ${neg:-CLEAN} | tighten-a: ${a:-none} | hold/close: ${hi:-CLEAN}" >> "$E"
    sed -n '/^proposal/,/^wrote/p' "$CA/$c.log" | head -40 > "$O/proposal_$c.txt"
    grep -E '^  [HI] +-[0-9]' "$f" | sort -u > "$O/report_hi_$c.txt"   # rows with their PAD values, for hold_pads.py
    grep -E '^  [A-Z]+ +[-+]?[0-9]' "$f" | sort -u > "$O/report_rows_$c.txt"   # every rule row (2026-11-15)
  else echo "static $c ERROR (see ca_$c.log)" >> "$E"; tail -30 "$CA/$c.log" > "$O/ca_$c.log"; fi
done
if [ -n "${SPEC_CASES:-}" ]; then
  for sc in ${SPEC_CASES//,/ }; do si=${sc%%:*}
    for cs in long short; do for m in nom worst; do f=$CA/${si}_${cs}_$m/report.txt
      if [ -f "$f" ]; then neg=$(awk '$1~/^(A|E)$/ && $2+0<0 && $3~/udut/ {print $1, $2, $3}' "$f" | sort -u | sed 's/bridge_i.udut.//' | tr '\n' ';')
        row=$(grep -E "^  A .*udut\.$si " "$f" | sort -u | head -1 | awk '{print $2, $4, $5}')
        echo "static-$cs $m ${neg:-CLEAN} | $si A' $row" >> "$E"
      else echo "static-$cs $m ERROR" >> "$E"; fi
    done; done
    for m in nom worst; do   # the select race inside the cell: abort vs the short line (spec_select.py)
      r=$(python3 "$R/research/tools/fifteen/spec_select.py" "$CA/$m/soak.sdf" "bridge_i.udut.$si" 2>&1 | tail -2 | tr "\n" " ")
      echo "select $m $r" >> "$E"; done
  done
fi
cat "$O"/gate_*.txt >> "$E" 2>/dev/null
[ -f "$O/hold_bits.tsv" ] && awk -F'\t' 'NR>1 && $4>0 {v=v $1"("$4"x,"$5"ps);"} NR==2 {m=$1" "$5} END {print "hold-bits violations: " (v?v:"none") " | tightest " m}' "$O/hold_bits.tsv" >> "$E"
[ -f "$O/hold.tsv" ] && awk -F'\t' 'NR>1 && $6>0 {v=v $1"("$6"x,"$7"ps);"} NR==2 {m=$1" "$7} END {print "hold violations: " (v?v:"none") " | tightest " m}' "$O/hold.tsv" >> "$E"
cat "$E"
