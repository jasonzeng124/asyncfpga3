#!/usr/bin/env bash
# s6_route.sh KERNEL SEED [COLS...] -- one of the farm's suite6 shipped routes, rebuilt and judged with the runt check:
#   1. rebuild from research/data/suite/resume/suite6/K_S/sizes_final.vh (= the shipped iteration's sizes), seed S,
#      BDC_AUTO=1 BDC_AUTO_REWRITES=1 (lane2.sh LANE_NORUN=1: the route + its prjxray SDF); the sdf md5 must equal the
#      farm's (result_suite6.txt);
#   2. the rule on it, exactly as auto_size.sh's rule() runs it (corner_audit CA_SIZERULE=1 at bands 0.20 and 0.31,
#      merged by merge_rules.py), with CA_FAST=1 (byte-identical outputs on these kernels, research/data/loopfast);
#      the corners one after the other (2 cores in all);
#   3. bench_gate.sh with GATE_RUNTS=1 at each COL (default: worst).
# Writes $RUNS/s6/K_S/{build.txt, rule (rule_0.20, rule_0.31, rule), gate_COL.txt, runts_COL.txt}.
set -uo pipefail
K=$1; S=$2; shift 2; COLS=${*:-worst}
R=$(cd "$(dirname "$0")/../../../.." && pwd); RUNS=${RUNS:?}; export RUNS
Z=$R/research/data/suite/resume/suite6/${K}_$S; N=s6_${K}_$S; O=$RUNS/s6/${K}_$S
mkdir -p "$RUNS/s6claim"; mkdir "$RUNS/s6claim/${K}_$S" 2>/dev/null || { echo "$N: claimed by another worker"; exit 0; }
mkdir -p "$O"
D=${K}_bench_gen; HW=$RUNS/hw/$N; RD=$RUNS/r/$N
case $K in
  xorshift) V=research/data/eventgraph/gate/xor19.hex; PV=research/data/fifteen/vec_xorshift.hex;;
  collatz) V=research/data/eventgraph/gate/col18.hex; PV=research/data/fifteen/vec_collatz.hex;;
  collatz64) V=research/data/eventgraph/gate/c6419.hex; PV=research/data/fifteen/vec_c64_871.hex;;
  ipow) V=research/data/eventgraph/gate/ipow17.hex; PV=research/data/fifteen/vec_ipow.hex;;
esac
want=$(tail -1 "$Z/result_suite6.txt" | awk '{for(i=1;i<=NF;i++) if($i ~ /^su_/ && $(i+1) ~ /^[0-9a-f]{8}$/) {print $(i+1); exit}}')
if [ ! -f "$RD/xray.sdf" ]; then
  LANE_NORUN=1 "$R/research/tools/fifteen/lane2.sh" L3 "$N" "$K" "$Z/sizes_final.vh" "$S" "$R/$PV" BDC_AUTO=1 BDC_AUTO_REWRITES=1 \
    > "$O/lane.log" 2>&1
fi
got=$(md5sum < "$HW/$D.sdf" | cut -c1-8)
echo "$N sdf $got farm $want $([ "$got" = "$want" ] && echo SAME || echo DIFFERENT)" | tee "$O/build.txt"
CA=$RUNS/ca/$N
if [ ! -f "$CA/rule/negative_sized.tsv" ]; then
  rm -rf "$CA"; mkdir -p "$CA/seed1/pnr"
  ln -sf "$RD/xray.sdf" "$CA/seed1/pnr/soak_xray.sdf"; ln -sf "$HW/${D}_routed.json" "$CA/seed1/pnr/soak_routed.json"
  cp "$Z/sizes_final.vh" "$CA/seed1/pnr/sizes.vh"
  for c in 0.20 0.31; do
    CA_FAST=1 PYTHONHASHSEED=1 BD_SKEW_STEER_SELF=1 CA_JOINAWARE=1 BD_SKEW_AND_JOIN=1 CA_SIZERULE=1 \
      python3 "$R/research/tools/corner_audit.py" "$CA/seed1" --prefix bridge_i.udut. \
        --band "$c" --inst-rx '\.chain\.g\[\d+\]\.u$:0.20' --out "$CA/rule_$c" > "$O/ca_$c.txt" 2>&1
  done
  python3 "$R/research/tools/auto/merge_rules.py" "$CA/rule" "$CA/rule_0.20" "$CA/rule_0.31" > "$O/merge.txt" 2>&1
fi
cp "$CA/rule/negative_sized.tsv" "$O/negative_sized.tsv" 2>/dev/null
for c in 0.20 0.31; do cp "$CA/rule_$c/report.txt" "$O/report_$c.txt" 2>/dev/null; done
echo "$N rule: $(($(grep -vc '^#' "$O/negative_sized.tsv" 2>/dev/null || echo 0))) negative sized row(s) (merged); suite6 said: $(tail -1 "$Z/result_suite6.txt" | cut -c1-40)" | tee -a "$O/build.txt"
"$R/research/tools/fifteen/kernel_oracle.sh" "$K" < "$R/$V" > "$O/exp.txt"
for col in $COLS; do
  W=$RUNS/g/$N/${col/:/_}; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
  GATE_RUNTS=1 "$R/research/tools/eventgraph/bench_gate.sh" "$HW" "$D" "$W" "$R/$V" "$O/exp.txt" "$col" > "$O/gate_${col/:/_}.txt" 2>&1
  tail -1 "$O/gate_${col/:/_}.txt"
  cp "$W/${col/:/_}/runts.txt" "$O/runts_${col/:/_}.txt" 2>/dev/null; rm -f "$W/${col/:/_}/"*.vcd
done
