#!/usr/bin/env bash
# auto_size.sh LANE NAME KERNEL SEED VEC [MAXIT] -- BDC_AUTO=1 with its sizes chosen by the flow: nothing per kernel
# (PROGRAM "General first", owner 2026-11-17: no sizes file, no factor, no instance name).
#
#   iteration 0  build with every matched delay at bdc/emit.py's estimate (est_sizes.py: the kernel's own defaults);
#                corner_audit.py CA_SIZERULE=1 on that route proposes every line (the one sizing rule: chain and
#                LUT / wire at one band, CARRY4 / F7F8 / FF at SLOW_MAX, the measured-residual guards, a shortened line
#                priced at its own mean step, selects sized by rules E / M like any line).
#   iteration i  build with the sizes S_i, run the same rule on the new route.  The route is CLEAN when no sized kernel
#                constraint is below slack on it as built (negative_sized.tsv empty).  S_{i+1} = ratchet.py(S_i,
#                proposal_i): a line the rule ever asked to lengthen is pinned at max(S_i, proposal_i), every other line
#                follows the proposal (shorter included).  The loop goes on while a clean route's proposal still
#                shortens a line, and stops at MAXIT, or when a negative route has no line the rule could lengthen.
#                It ships the LAST CLEAN route (else the last route, NOT CLEAN).
#   The rule runs with BD_SKEW_AND_JOIN=1: a bd_ctree C-element fires on its LAST input, as built (audit T93: the
#   OR seeding made ucond_br6_j fire on its first request); the hand recipes' farm requests used it too.
#
# Why a loop: sizes belong to one route, and the route built from them is a different one (cells/hw/tighten_loop.sh's
# header: a 24-element line re-placed as 8 elements got 27 % cheaper per element, so a proposal priced on the long line
# under-delivers, in the short direction).  CA_SIZERULE prices a shortened line at its own mean step on purpose (the
# default price, the route's single cheapest hop, is the 1.6-2x term in research/data/sizerule/README.md), so this
# re-check of the route actually built is what makes it safe.  Why the pinning: without it the loop oscillates
# (tighten_loop.sh, measured: shortened, found short, padded, shortened again); a pinned line cannot be shortened again.
# Why not pin every line (the first version): the first proposal is made on the estimates route, the most spread-out
# route the loop sees, and pinning it everywhere kept its pessimism (ratchet.py's header).
# Every iteration is a lane2.sh build with LANE_NORUN=1 (the route and its prjxray SDF, which is all the rule reads);
# the full stack (bits-decoded netlist, equivalence, fid run, event-graph period P) runs once, on the route kept
# (lane2_run.sh).  CA_JOBS=N (environment) runs corner_audit's per-line sensitivity workers N at a time.
#
# Writes $RUNS/auto/NAME/{sizes_I.vh, it_I.txt, ca_I.txt, result.txt}.  result.txt: "CLEAN it=I route=NAME_I P=.."
# or "NOT CLEAN after MAXIT".  The shipped route's files are $RUNS/hw/NAME_I, $RUNS/r/NAME_I (lane2.sh).
set -uo pipefail
L=$1; N=$2; K=$3; S=$4; VEC=$5; MAXIT=${6:-4}
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/home/user/runs}; export RUNS
LANE=$R/research/tools/fifteen/lane2.sh; T=$R/research/tools/auto
O=$RUNS/auto/$N; mkdir -p "$O"; : > "$O/result.txt"
D=${K}_bench_gen
rule() {   # rule I SIZES: corner_audit CA_SIZERULE=1 on route NAME_I as built with SIZES
  local i=$1 Z=$2 NI=${N}_$1; local HW=$RUNS/hw/$NI RD=$RUNS/r/$NI CA=$RUNS/ca/$NI
  rm -rf "$CA"; mkdir -p "$CA/seed1/pnr"
  ln -sf "$RD/xray.sdf" "$CA/seed1/pnr/soak_xray.sdf"; ln -sf "$HW/${D}_routed.json" "$CA/seed1/pnr/soak_routed.json"
  cp "$Z" "$CA/seed1/pnr/sizes.vh"
  BD_SKEW_AND_JOIN=1 CA_SIZERULE=1 python3 "$R/research/tools/corner_audit.py" "$CA/seed1" --prefix bridge_i.udut. --out "$CA/rule" \
      > "$O/ca_$i.txt" 2>&1
  [ -f "$CA/rule/sizes.vh" ] && [ -f "$CA/rule/negative_sized.tsv" ]
}
build() {  # build I SIZES: the route and its prjxray SDF only (LANE_NORUN=1); final() runs the full stack on the kept one
  local i=$1 Z=$2
  LANE_NORUN=1 "$LANE" "$L" "${N}_$i" "$K" "$Z" "$S" "$VEC" BDC_AUTO=1 > "$O/it_$i.log" 2>&1
  tail -1 "$O/it_$i.log" > "$O/it_$i.txt"
  [ -f "$RUNS/r/${N}_$i/xray.sdf" ] && [ -f "$RUNS/hw/${N}_$i/${D}_routed.json" ]
}
final() {  # final I: the full stack (bits-decoded netlist, equivalence, fid run, event-graph P) on the route the loop keeps
  local i=$1
  "$R/research/tools/fifteen/lane2_run.sh" "${N}_$i" "$K" "$VEC" BDC_AUTO=1 > "$O/final_$i.log" 2>&1
  tail -1 "$O/final_$i.log" > "$O/it_$i.txt"
  echo "final it $i $(cat "$O/it_$i.txt")" >> "$O/log.txt"
}
echo "auto_size $N kernel $K seed $S maxit $MAXIT $(date -u +%FT%TZ) head $(git -C "$R" rev-parse --short HEAD)" > "$O/log.txt"
build 0 none || { echo "BUILD FAILED it=0" | tee -a "$O/result.txt"; exit 1; }
python3 "$T/est_sizes.py" "$RUNS/hw/${N}_0/${K}_kernel_bench.v" "$K" > "$O/sizes_0.vh" || { echo "NO ESTIMATES" >> "$O/result.txt"; exit 1; }
echo "it 0 $(cat "$O/it_0.txt") lines $(grep -c '^`define' "$O/sizes_0.vh")" >> "$O/log.txt"
rule 0 "$O/sizes_0.vh" || { echo "RULE FAILED it=0" | tee -a "$O/result.txt"; exit 1; }
cp "$RUNS/ca/${N}_0/rule/sizes.vh" "$O/sizes_1.vh"
echo "it 0 rule: $(grep -c . "$RUNS/ca/${N}_0/rule/negative_sized.tsv") negative rows (incl. header); $(grep '^proposal' "$O/ca_0.txt")" >> "$O/log.txt"
rm -f "$O/pinned.txt"; LC=""
for i in $(seq 1 "$MAXIT"); do
  build "$i" "$O/sizes_$i.vh" || { echo "BUILD FAILED it=$i" | tee -a "$O/result.txt"; exit 1; }
  rule "$i" "$O/sizes_$i.vh" || { echo "RULE FAILED it=$i" | tee -a "$O/result.txt"; exit 1; }
  st=$(python3 "$T/ratchet.py" "$O/sizes_$i.vh" "$RUNS/ca/${N}_$i/rule/sizes.vh" "$RUNS/ca/${N}_$i/rule/negative_sized.tsv" \
       "$O/sizes_$((i + 1)).vh" "$O/pinned.txt")
  echo "it $i $(cat "$O/it_$i.txt") | $(echo "$st" | head -1)" >> "$O/log.txt"
  echo "$st" > "$O/ratchet_$i.txt"
  read -r _ nr _ _ _ neg _ nl _ _ <<< "$(echo "$st" | head -1)"
  if [ "$neg" = 0 ]; then LC=$i; [ "$nl" = 0 ] && break; fi   # clean; go on only while the proposal still shortens
  if [ "$neg" != 0 ] && [ "$nr" = 0 ]; then break; fi        # negative and nothing the rule can lengthen
done
if [ -n "$LC" ]; then
  final "$LC"; cp "$O/sizes_$LC.vh" "$O/sizes_final.vh"
  echo "CLEAN it=$LC route=${N}_$LC (last it $i) $(cat "$O/it_$LC.txt")" | tee -a "$O/result.txt"; exit 0
fi
final "$i"; cp "$O/sizes_$i.vh" "$O/sizes_final.vh"
if [ "$nr" = 0 ]; then
  echo "NOT CLEAN it=$i: $neg negative, none fixable by a line (route ${N}_$i) $(cat "$O/it_$i.txt")" | tee -a "$O/result.txt"; exit 3
fi
echo "NOT CLEAN after $i (last route ${N}_$i; next sizes sizes_$((i + 1)).vh) $(cat "$O/it_$i.txt")" | tee -a "$O/result.txt"
exit 2
