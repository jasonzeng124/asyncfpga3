#!/usr/bin/env bash
# auto_size.sh LANE NAME KERNEL SEED VEC [MAXIT] -- BDC_AUTO=1 with its sizes chosen by the flow: nothing per kernel
# (PROGRAM "General first", owner 2026-11-17: no sizes file, no factor, no instance name).
#
#   iteration 0  build with every matched delay at bdc/emit.py's estimate (est_sizes.py: the kernel's own defaults)
#                times AUTO_START_SCALE (0.3; see below);
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
  # The rule at the delay model's worst vertices (AUTO_RULE_CORNERS, default "0.20 0.31": the band of everything but the
  # delay chains, the chains at 0.20, CARRY4 / F7F8 / FF at SLOW_MAX), merged per line by the max (merge_rules.py).
  # Why two: bench_gate.sh's draws -- the judge -- take the chains and the rest independently from [0.20, 0.31]; a
  # race's margin is linear in the two bands, the chains sit on the request side (worst at 0.20), the rest on both
  # sides (worst at either end).  One band for both (CA_SIZERULE's own default, 0.21) sized xorshift seed 8's entry
  # compare UCMPI0 at 5, and the draw with chains 0.212 / rest 0.277 got the zero-trip call wrong (farm suite1).
  # CA_JOINAWARE=1 (default here; research/data/sizerule/joinaware.md): rule A' checks an operator's data where it is
  # captured, with a sibling's request credited at a shared join (formal B2 / B3: the incrementer paid for a capture
  # that does not happen). xorshift seed 1's final route, both corners: 103 -> 89 links (UADDI0 7 -> 1).
  # BD_SKEW_STEER_SELF=1 (default here; research/data/sizerule/steerE.md): at a steer whose C-element join carries the
  # select's own channel request, rule E from a latch launch is bounded by that request; the row that held xorshift's
  # loop test UCMPI1 at 17-19 was a lap through the steer's own select and a sibling's acknowledge (17 -> 8; a build at
  # those sizes 16.62 ns vs 21.08, 4/4 draws).
  # BD_SKEW_E_JOIN=1 (opt-in, default OFF; research/data/sizerule/ejoin.md): rule E credits a C-element on the request
  # path with its other inputs' arrivals, case by case on what made the launch fire (BD_SKEW_E_JOIN_DEPTH causes back,
  # default 1).  Passed through from the environment; unset, the rule is byte-identical.
  local c; for c in ${AUTO_RULE_CORNERS:-0.20 0.31}; do
    BD_SKEW_E_JOIN=${BD_SKEW_E_JOIN:-} BD_SKEW_E_JOIN_DEPTH=${BD_SKEW_E_JOIN_DEPTH:-1} \
    BD_SKEW_STEER_SELF=${BD_SKEW_STEER_SELF:-1} CA_JOINAWARE=${CA_JOINAWARE:-1} BD_SKEW_AND_JOIN=1 CA_SIZERULE=1 \
      python3 "$R/research/tools/corner_audit.py" "$CA/seed1" --prefix bridge_i.udut. \
        --band "$c" --inst-rx '\.chain\.g\[\d+\]\.u$:0.20' --out "$CA/rule_$c" > "$O/ca_${i}_$c.txt" 2>&1 &
  done; wait
  local dirs=(); for c in ${AUTO_RULE_CORNERS:-0.20 0.31}; do
    [ -f "$CA/rule_$c/sizes.vh" ] && [ -f "$CA/rule_$c/negative_sized.tsv" ] || return 1; dirs+=("$CA/rule_$c"); done
  python3 "$T/merge_rules.py" "$CA/rule" "${dirs[@]}" && grep -h '^proposal' "$O/ca_${i}_"*.txt > "$O/ca_$i.txt"
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
# The start: bdc/emit.py's estimates ("deliberately generous", bdc/compute.py) times AUTO_START_SCALE (default 0.3, one
# number for every kernel: it moves only where the loop starts; the rule on each route sets the sizes).  Why: on the
# first kernels the estimates are 4-5x the sizes the loop ends at (seed 1: xorshift 511 -> 106 links, collatz 493 ->
# ~100, collatz64 647 -> ~130); the route built at them is the most spread-out the loop sees, its long wires stand in
# for data the compact routes must cover (collatz64's 3n + 1: proposed 4 elements there, needed 20 on the next route),
# and on 2 cores it can take over an hour to route (farm suite1: collatz seeds 3 and 4 hit PNR_TIMEOUT 3600 at it 0).
# AUTO_START_SCALE=1 starts at the estimates (the first version).
SC=${AUTO_START_SCALE:-0.3}
EM=$O/emit; mkdir -p "$EM"   # the estimates: the same two steps as cells/hw/build_bench.sh with BDC_AUTO=1
python3 "$R/bdc/auto.py" "$R/build/frontend/$K/comp/handshake_transformed.mlir" "$EM/auto.mlir" > "$EM/auto.log" 2>&1 \
  && BDC_AUTO=1 python3 "$R/bdc/emit.py" "$EM/auto.mlir" --no-top -o "$EM/kernel.v" >> "$EM/auto.log" 2>&1 \
  && python3 "$T/est_sizes.py" "$EM/kernel.v" "$K" > "$O/sizes_est.vh" \
  || { echo "BUILD FAILED it=0 (emit: $(tail -1 "$EM/auto.log"))" | tee -a "$O/result.txt"; exit 1; }
if [ "$SC" = 1 ]; then cp "$O/sizes_est.vh" "$O/sizes_0.vh"
else python3 "$R/research/tools/shrink_sizes.py" "$O/sizes_est.vh" "$SC" "$O/sizes_0.vh" > /dev/null; fi
build 0 "$O/sizes_0.vh" || { echo "BUILD FAILED it=0" | tee -a "$O/result.txt"; exit 1; }
echo "it 0 $(cat "$O/it_0.txt") lines $(grep -c '^`define' "$O/sizes_0.vh")" >> "$O/log.txt"
rule 0 "$O/sizes_0.vh" || { echo "RULE FAILED it=0" | tee -a "$O/result.txt"; exit 1; }
cp "$RUNS/ca/${N}_0/rule/sizes.vh" "$O/sizes_1.vh"
echo "it 0 rule: $(grep -c . "$RUNS/ca/${N}_0/rule/negative_sized.tsv") negative rows (incl. header); $(grep '^proposal' "$O/ca_0.txt")" >> "$O/log.txt"
rm -f "$O/pinned.txt"; LC=""; FIN=${AUTO_FINISH:-3}
# Phase 1 (i = 1..MAXIT): the pinning ratchet; go on while a clean route still shortens a line.
# Phase 2, only when no route was clean by MAXIT (i = MAXIT+1..MAXIT+FIN): raise-only (every line max(S, proposal)), so
# no lowering opens new misses, until a route is clean.  Why: the loop used to ship its last route NOT CLEAN, and
# formal B7 found a wrong answer on such a route exactly at the race the rule flagged (suite1 xorshift seed 3: entry
# compare UCMPI0 6, the rule's raise to 7 never built; slow-carry draw 5104 returns 0x92d78cb6 on the zero-trip call).
i=0; ph=1
while :; do
  i=$((i + 1))
  build "$i" "$O/sizes_$i.vh" || { echo "BUILD FAILED it=$i" | tee -a "$O/result.txt"; exit 1; }
  rule "$i" "$O/sizes_$i.vh" || { echo "RULE FAILED it=$i" | tee -a "$O/result.txt"; exit 1; }
  # phase 2 raises with one element of headroom: each re-route moves the small margins by a few hundred ps (local v4
  # xorshift seed 8: 5, 3, 4 constraints short at -5..-278 ps on three raise-only routes), about one element
  ro=""; [ "$ph" = 2 ] && ro="--raise-only --headroom ${AUTO_HEADROOM:-1}"
  # it 1 is a recalibration: the start's proposal under-delivers on the compact route it produces (xorshift seed 2,
  # flow v5: 50 constraints short at it 1), so its raises are not oscillation; pinning them kept UCMPI1 at 15 for good
  # (the loop ended at 129 links / 23.0 ns where v2 had 103 / 16.7). Pinning starts at it 2.
  [ "$i" = 1 ] && [ "$ph" = 1 ] && ro="--nopin"
  st=$(python3 "$T/ratchet.py" "$O/sizes_$i.vh" "$RUNS/ca/${N}_$i/rule/sizes.vh" "$RUNS/ca/${N}_$i/rule/negative_sized.tsv" \
       "$O/sizes_$((i + 1)).vh" "$O/pinned.txt" $ro)
  echo "it $i $(cat "$O/it_$i.txt") | $(echo "$st" | head -1)${ro:+ ($ro)}" >> "$O/log.txt"
  echo "$st" > "$O/ratchet_$i.txt"
  read -r _ nr _ _ _ neg _ nl _ _ <<< "$(echo "$st" | head -1)"
  if [ "$neg" = 0 ]; then LC=$i; [ "$nl" = 0 ] || [ "$ph" = 2 ] && break; fi   # clean: done, or go on while it shortens
  if [ "$neg" != 0 ] && [ "$nr" = 0 ]; then break; fi        # negative and nothing the rule can lengthen
  if [ "$ph" = 1 ] && [ "$i" -ge "$MAXIT" ]; then
    [ -n "$LC" ] && break
    [ "$FIN" -gt 0 ] || break
    ph=2; IMAX=$((MAXIT + FIN))
    # the next sizes without the lowering phase 1's last ratchet did
    python3 "$T/ratchet.py" "$O/sizes_$i.vh" "$RUNS/ca/${N}_$i/rule/sizes.vh" "$RUNS/ca/${N}_$i/rule/negative_sized.tsv" \
       "$O/sizes_$((i + 1)).vh" "$O/pinned.txt" --raise-only --headroom "${AUTO_HEADROOM:-1}" > /dev/null
    echo "phase 2 (raise-only) from it $((i + 1))" >> "$O/log.txt"
  elif [ "$ph" = 2 ] && [ "$i" -ge "$IMAX" ]; then break; fi
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
