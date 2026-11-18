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
# AUTO_RESUME=DIR (environment) continues a loop another run left unfinished (a farm task stopped at its time limit):
# DIR holds that run's $RUNS/auto/NAME files as the farm returns them (*.txt, *.vh: log.txt, sizes_I.vh, pinned.txt,
# ratchet_I.txt, rule_I.vh, neg_I.txt). The loop goes on from the last iteration whose ratchet step was written, in the
# phase the log names, replaying that iteration's stop / phase decision; a route it needs again (the one it ships) is
# rebuilt from its sizes with the same seed, which gives the same route (checked: the sdf md5 must match it_I.txt).
# Unset: the loop as before (it also saves rule_I.vh and neg_I.txt, the rule's proposal and negatives, for a resume).
#
# AUTO_NEAR_PS=PS (opt-in; unset = as before): in the finish phase (raise-only) every line the rule keeps at its size with
# fewer than PS ps left at a corner gets the headroom element too, not only the lines that are short (ratchet.py --near).
#
# Writes $RUNS/auto/NAME/{sizes_I.vh, it_I.txt, ca_I.txt, result.txt}.  result.txt: "CLEAN it=I route=NAME_I P=.."
# or "NOT CLEAN after MAXIT".  The shipped route's files are $RUNS/hw/NAME_I, $RUNS/r/NAME_I (lane2.sh).
set -uo pipefail
L=$1; N=$2; K=$3; S=$4; VEC=$5; MAXIT=${6:-4}
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/home/user/runs}; export RUNS
LANE=$R/research/tools/fifteen/lane2.sh; T=$R/research/tools/auto
O=$RUNS/auto/$N; mkdir -p "$O"
RES=""
XENV=""   # the structure AUTO_SEARCH=1 chose (BDC_LINK_DEPTHS=...); empty unless its phase picked an edit
if [ -n "${AUTO_RESUME:-}" ] && [ -f "$AUTO_RESUME/sizes_1.vh" ]; then
  RES=$(cd "$AUTO_RESUME" && pwd)
  [ "$RES" = "$(cd "$O" && pwd)" ] || cp "$RES"/*.txt "$RES"/*.vh "$O/" 2>/dev/null
fi
: > "$O/result.txt"
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
  [ -f "$CA/rule/sizes.vh" ] && [ -f "$CA/rule/negative_sized.tsv" ] || return 1
  cp "$CA/rule/sizes.vh" "$O/rule_$i.vh"; cp "$CA/rule/negative_sized.tsv" "$O/neg_$i.txt"   # for AUTO_RESUME
  for c in ${AUTO_RULE_CORNERS:-0.20 0.31}; do cp "$CA/rule_$c/lines.tsv" "$O/lines_${i}_$c.txt" 2>/dev/null; done
}
near_args() {  # near_args I: AUTO_NEAR_PS (opt-in): the finish phase also pads every line with < AUTO_NEAR_PS ps left
  [ -n "${AUTO_NEAR_PS:-}" ] || return 0
  local c l=""; for c in ${AUTO_RULE_CORNERS:-0.20 0.31}; do l="$l${l:+,}$O/lines_${1}_$c.txt"; done
  echo "--near $AUTO_NEAR_PS $l"
}
build() {  # build I SIZES: the route and its prjxray SDF only (LANE_NORUN=1); final() runs the full stack on the kept one
  local i=$1 Z=$2
  LANE_NORUN=1 "$LANE" "$L" "${N}_$i" "$K" "$Z" "$S" "$VEC" BDC_AUTO=1 ${XENV:-} > "$O/it_$i.log" 2>&1
  tail -1 "$O/it_$i.log" > "$O/it_$i.txt"
  [ -f "$RUNS/r/${N}_$i/xray.sdf" ] && [ -f "$RUNS/hw/${N}_$i/${D}_routed.json" ]
}
final() {  # final I: the full stack (bits-decoded netlist, equivalence, fid run, event-graph P) on the route the loop keeps
  local i=$1
  if [ ! -f "$RUNS/r/${N}_$i/xray.sdf" ]; then   # AUTO_RESUME: the route was built by an earlier run; rebuild it
    local want; want=$(awk '{print $2}' "$O/it_$i.txt" 2>/dev/null)
    cp "$O/it_$i.txt" "$O/it_${i}_before_resume.txt" 2>/dev/null
    build "$i" "$O/sizes_$i.vh" || { echo "BUILD FAILED it=$i (rebuild for the final stack)" | tee -a "$O/result.txt"; exit 1; }
    local got; got=$(awk '{print $2}' "$O/it_$i.txt")
    echo "resume: route ${N}_$i rebuilt, sdf $got (earlier run: ${want:-?})$([ -n "$want" ] && [ "$want" != "$got" ] && echo ' -- DIFFERENT ROUTE')" >> "$O/log.txt"
  fi
  "$R/research/tools/fifteen/lane2_run.sh" "${N}_$i" "$K" "$VEC" BDC_AUTO=1 ${XENV:-} > "$O/final_$i.log" 2>&1
  tail -1 "$O/final_$i.log" > "$O/it_$i.txt"
  echo "final it $i $(cat "$O/it_$i.txt")" >> "$O/log.txt"
}
if [ -n "$RES" ]; then
  echo "auto_size $N RESUMED from $RES $(date -u +%FT%TZ) head $(git -C "$R" rev-parse --short HEAD)" >> "$O/log.txt"
else
  echo "auto_size $N kernel $K seed $S maxit $MAXIT $(date -u +%FT%TZ) head $(git -C "$R" rev-parse --short HEAD)" > "$O/log.txt"
fi
# The start: bdc/emit.py's estimates ("deliberately generous", bdc/compute.py) times AUTO_START_SCALE (default 0.3, one
# number for every kernel: it moves only where the loop starts; the rule on each route sets the sizes).  Why: on the
# first kernels the estimates are 4-5x the sizes the loop ends at (seed 1: xorshift 511 -> 106 links, collatz 493 ->
# ~100, collatz64 647 -> ~130); the route built at them is the most spread-out the loop sees, its long wires stand in
# for data the compact routes must cover (collatz64's 3n + 1: proposed 4 elements there, needed 20 on the next route),
# and on 2 cores it can take over an hour to route (farm suite1: collatz seeds 3 and 4 hit PNR_TIMEOUT 3600 at it 0).
# AUTO_START_SCALE=1 starts at the estimates (the first version).
# bd_mem's two lines (USETUP, UCO: the RAM's address setup and clock-to-out / address hold, bdc/mem.py) are NOT scaled
# (AUTO_START_ONLY, a shrink_sizes.py --only regex): the rule cannot size them -- corner_audit names the chain
# <port>_uport.umem<k>.uco (BD_SZ_..._UPORT_UMEM0_UCO), emit.py's macro is BD_SZ_..._UMEM0_UCO ("sizes.vh does not
# set (kept, measured)") -- so a scaled value was never raised again: every memory kernel shipped DSETUP 3 / DCO 4
# (estimates 8 / 12), and on test_bitint seed 1 the rule's C check read -1.2 .. -1.9 ns on both RAMs, "STILL SHORT",
# on every route of the loop (suitew, 2026-11-18).
if [ -z "$RES" ]; then
SC=${AUTO_START_SCALE:-0.3}; ONLY=${AUTO_START_ONLY:-'^(?!.*_UMEM[0-9]+_(USETUP|UCO)$)'}
EM=$O/emit; mkdir -p "$EM"   # the estimates: the same two steps as cells/hw/build_bench.sh with BDC_AUTO=1
python3 "$R/bdc/auto.py" "$R/build/frontend/$K/comp/handshake_transformed.mlir" "$EM/auto.mlir" > "$EM/auto.log" 2>&1 \
  && BDC_AUTO=1 python3 "$R/bdc/emit.py" "$EM/auto.mlir" --no-top -o "$EM/kernel.v" >> "$EM/auto.log" 2>&1 \
  && python3 "$T/est_sizes.py" "$EM/kernel.v" "$K" > "$O/sizes_est.vh" \
  || { echo "BUILD FAILED it=0 (emit: $(tail -1 "$EM/auto.log"))" | tee -a "$O/result.txt"; exit 1; }
if [ "$SC" = 1 ]; then cp "$O/sizes_est.vh" "$O/sizes_0.vh"
else python3 "$R/research/tools/shrink_sizes.py" "$O/sizes_est.vh" "$SC" "$O/sizes_0.vh" --only "$ONLY" > /dev/null; fi
build 0 "$O/sizes_0.vh" || { echo "BUILD FAILED it=0" | tee -a "$O/result.txt"; exit 1; }
echo "it 0 $(cat "$O/it_0.txt") lines $(grep -c '^`define' "$O/sizes_0.vh")" >> "$O/log.txt"
rule 0 "$O/sizes_0.vh" || { echo "RULE FAILED it=0" | tee -a "$O/result.txt"; exit 1; }
if ! grep -q '^`define' "$O/sizes_est.vh"; then
  # Nothing to size: the kernel has no matched delay (est_sizes.py; test_int16, a constant joined with the call's end
  # token).  Every further route would be the same circuit, so the route built at it 0 is the one judged: CLEAN when
  # the rule finds no negative kernel constraint on it, else NOT CLEAN with no line that could fix it.
  neg=$(tail -n +2 "$RUNS/ca/${N}_0/rule/negative_sized.tsv" | grep -c .)
  echo "it 0 rule: nothing to size (no matched delay); $neg negative rows" >> "$O/log.txt"
  final 0; cp "$O/sizes_0.vh" "$O/sizes_final.vh"
  if [ "$neg" = 0 ]; then
    echo "CLEAN it=0 route=${N}_0 (nothing to size) $(cat "$O/it_0.txt")" | tee -a "$O/result.txt"; exit 0
  fi
  echo "NOT CLEAN it=0: $neg negative, none fixable by a line (nothing to size; route ${N}_0) $(cat "$O/it_0.txt")" \
    | tee -a "$O/result.txt"; exit 3
fi
cp "$RUNS/ca/${N}_0/rule/sizes.vh" "$O/sizes_1.vh"
echo "it 0 rule: $(grep -c . "$RUNS/ca/${N}_0/rule/negative_sized.tsv") negative rows (incl. header); $(grep '^proposal' "$O/ca_0.txt")" >> "$O/log.txt"
fi
[ -n "$RES" ] || rm -f "$O/pinned.txt"
LC=""; FIN=${AUTO_FINISH:-3}
# Phase 1 (i = 1..MAXIT): the pinning ratchet; go on while a clean route still shortens a line.
# Phase 2, only when no route was clean by MAXIT (i = MAXIT+1..MAXIT+FIN): raise-only (every line max(S, proposal)), so
# no lowering opens new misses, until a route is clean.  Why: the loop used to ship its last route NOT CLEAN, and
# formal B7 found a wrong answer on such a route exactly at the race the rule flagged (suite1 xorshift seed 3: entry
# compare UCMPI0 6, the rule's raise to 7 never built; slow-carry draw 5104 returns 0x92d78cb6 on the zero-trip call).
i=0; ph=1; STOP=""
if [ -n "$RES" ]; then
  # the last iteration whose ratchet step was written; the phase the log names; then that iteration's decision again
  for f in "$O"/ratchet_*.txt; do [ -f "$f" ] || continue; k=${f##*/ratchet_}; k=${k%.txt}
    case $k in *[!0-9]*) continue;; esac; [ "$k" -gt "$i" ] && i=$k; done
  grep -q '^phase 2 (raise-only) from it' "$O/log.txt" && { ph=2; IMAX=$((MAXIT + FIN)); }
  for k in $(seq 1 "$i"); do
    [ -f "$O/ratchet_$k.txt" ] || continue
    read -r _ _ _ _ _ ng _ _ _ _ <<< "$(head -1 "$O/ratchet_$k.txt")"; [ "$ng" = 0 ] && LC=$k
  done
  if [ "$i" -ge 1 ] && [ -f "$O/pinned_$i.txt" ]; then cp "$O/pinned_$i.txt" "$O/pinned.txt"
  elif [ "$i" -ge 1 ]; then echo "resume: no pinned_$i.txt (an older run): pinned.txt as copied, possibly later than it $i" >> "$O/log.txt"
  else : > "$O/pinned.txt"; fi
  echo "resume: last ratchet it $i, phase $ph, last clean ${LC:-none}" >> "$O/log.txt"
  if [ "$i" -ge 1 ]; then
    read -r _ nr _ _ _ neg _ nl _ _ <<< "$(head -1 "$O/ratchet_$i.txt")"
    if [ "$neg" = 0 ] && { [ "$nl" = 0 ] || [ "$ph" = 2 ]; }; then STOP=1
    elif [ "$neg" != 0 ] && [ "$nr" = 0 ]; then STOP=1
    elif [ "$ph" = 1 ] && [ "$i" -ge "$MAXIT" ]; then
      if [ -n "$LC" ] || [ "$FIN" -le 0 ]; then STOP=1
      elif [ ! -f "$O/rule_$i.vh" ]; then STOP=1; echo "resume: phase 2 due but no rule_$i.vh to switch with" >> "$O/log.txt"
      else
        ph=2; IMAX=$((MAXIT + FIN))
        python3 "$T/ratchet.py" "$O/sizes_$i.vh" "$O/rule_$i.vh" "$O/neg_$i.txt" \
           "$O/sizes_$((i + 1)).vh" "$O/pinned.txt" --raise-only --headroom "${AUTO_HEADROOM:-1}" $(near_args "$i") > /dev/null
        echo "phase 2 (raise-only) from it $((i + 1))" >> "$O/log.txt"
      fi
    elif [ "$ph" = 2 ] && [ "$i" -ge "$IMAX" ]; then STOP=1; fi
  fi
  [ -f "$O/sizes_$((i + 1)).vh" ] || STOP=1
fi
while [ -z "$STOP" ]; do
  i=$((i + 1))
  build "$i" "$O/sizes_$i.vh" || { echo "BUILD FAILED it=$i" | tee -a "$O/result.txt"; exit 1; }
  rule "$i" "$O/sizes_$i.vh" || { echo "RULE FAILED it=$i" | tee -a "$O/result.txt"; exit 1; }
  # phase 2 raises with one element of headroom: each re-route moves the small margins by a few hundred ps (local v4
  # xorshift seed 8: 5, 3, 4 constraints short at -5..-278 ps on three raise-only routes), about one element
  ro=""; [ "$ph" = 2 ] && ro="--raise-only --headroom ${AUTO_HEADROOM:-1} $(near_args "$i")"
  # it 1 is a recalibration: the start's proposal under-delivers on the compact route it produces (xorshift seed 2,
  # flow v5: 50 constraints short at it 1), so its raises are not oscillation; pinning them kept UCMPI1 at 15 for good
  # (the loop ended at 129 links / 23.0 ns where v2 had 103 / 16.7). Pinning starts at it 2.
  [ "$i" = 1 ] && [ "$ph" = 1 ] && ro="--nopin"
  st=$(python3 "$T/ratchet.py" "$O/sizes_$i.vh" "$RUNS/ca/${N}_$i/rule/sizes.vh" "$RUNS/ca/${N}_$i/rule/negative_sized.tsv" \
       "$O/sizes_$((i + 1)).vh" "$O/pinned.txt" $ro)
  echo "it $i $(cat "$O/it_$i.txt") | $(echo "$st" | head -1)${ro:+ ($ro)}" >> "$O/log.txt"
  read -r _ nr _ _ _ neg _ nl _ _ <<< "$(echo "$st" | head -1)"
  brk=""
  if [ "$neg" = 0 ]; then LC=$i; { [ "$nl" = 0 ] || [ "$ph" = 2 ]; } && brk=1; fi   # clean: done, or go on while it shortens
  if [ -z "$brk" ] && [ "$neg" != 0 ] && [ "$nr" = 0 ]; then brk=1; fi        # negative and nothing the rule can lengthen
  if [ -z "$brk" ] && [ "$ph" = 1 ] && [ "$i" -ge "$MAXIT" ]; then
    if [ -n "$LC" ] || [ "$FIN" -le 0 ]; then brk=1
    else
      ph=2; IMAX=$((MAXIT + FIN))
      # the next sizes without the lowering phase 1's last ratchet did
      python3 "$T/ratchet.py" "$O/sizes_$i.vh" "$RUNS/ca/${N}_$i/rule/sizes.vh" "$RUNS/ca/${N}_$i/rule/negative_sized.tsv" \
         "$O/sizes_$((i + 1)).vh" "$O/pinned.txt" --raise-only --headroom "${AUTO_HEADROOM:-1}" $(near_args "$i") > /dev/null
      echo "phase 2 (raise-only) from it $((i + 1))" >> "$O/log.txt"
    fi
  elif [ -z "$brk" ] && [ "$ph" = 2 ] && [ "$i" -ge "$IMAX" ]; then brk=1; fi
  # ratchet_I.txt LAST: its presence says iteration I is complete (sizes_I+1, the pins, a phase switch) for AUTO_RESUME
  cp "$O/pinned.txt" "$O/pinned_$i.txt" 2>/dev/null || : > "$O/pinned_$i.txt"
  echo "$st" > "$O/ratchet_$i.txt"
  [ -n "$brk" ] && break
done
# Phase 3 (AUTO_SEARCH=1, opt-in; unset, nothing below runs and the loop ships as before): the event graph's storage
# search inside the flow (PROGRAM "General first" 1: "where the latches go and how deep the links are (the event graph's
# search, run inside the flow)"; research/data/auto/README.md: "Not done: the search inside the flow").  final() has
# built the timed event graph of the route the loop ships (its P); research/tools/eventgraph/search.py --depth-only
# takes, greedily, each BDC_LINK_DEPTHS +1 that graph predicts to gain >= 300 ps.  Nothing is named by hand: the search
# names links from the measured graph of this kernel's own route.  Why: the one structural difference between the hand
# xorshift recipe (board item 37, 16.76 ns) and the automatic one is ulink_n_trueResult_8 at 2 stages (x's back edge),
# left out of bdc/auto.py because a static rule for it would also hit collatz (+675 ps there); the search picks exactly
# it on every automatic xorshift route it was run on (research/data/auto/xorgap.md).  If it picks an edit, the loop goes
# on with that structure from the shipped sizes (a new line -- a deepened link's SDELAY -- starts as every line did, at
# emit.py's estimate x AUTO_START_SCALE; pinned.txt carries over) for AUTO_SEARCH_MAXIT routes (default 4, the last two
# raise-only with headroom, as phase 2), and its last clean route gets the full stack.  The flow ships that route if it
# is clean and its measured P is below the first route's (or the first was not clean); else the first, as without the
# search.  log.txt has both.
search_phase() {
  local G=$R/research/data/eventgraph/graphs/${N}_$X EM3=$O/emit3 k=0 j LC3="" ro st nr3 neg3 nl3 P0 P3
  local M3=${AUTO_SEARCH_MAXIT:-4} SC3=${AUTO_START_SCALE:-0.3} ONLY3=${AUTO_START_ONLY:-'^(?!.*_UMEM[0-9]+_(USETUP|UCO)$)'}
  if ! grep -q "period P = [0-9]" "$G/check.txt" 2>/dev/null; then
    echo "search: no event graph for route ${N}_$X: skipped" >> "$O/log.txt"; return 0; fi
  python3 "$R/research/tools/eventgraph/search.py" "$G" "$O/sizes_$X.vh" --depth-only > "$O/search.txt" 2>&1
  XENV=$(sed -n 's/^ENV //p' "$O/search.txt")
  echo "search on ${N}_$X: $(grep -E '^(base|chosen)' "$O/search.txt" | tr '\n' ' ')" >> "$O/log.txt"
  [ -n "$XENV" ] || return 0
  mkdir -p "$EM3"
  python3 "$R/bdc/auto.py" "$R/build/frontend/$K/comp/handshake_transformed.mlir" "$EM3/auto.mlir" > "$EM3/log" 2>&1 \
    && env $XENV BDC_AUTO=1 python3 "$R/bdc/emit.py" "$EM3/auto.mlir" --no-top -o "$EM3/kernel.v" >> "$EM3/log" 2>&1 \
    && python3 "$T/est_sizes.py" "$EM3/kernel.v" "$K" > "$EM3/est.vh" \
    && python3 "$R/research/tools/shrink_sizes.py" "$EM3/est.vh" "$SC3" "$EM3/start.vh" --only "$ONLY3" > /dev/null \
    || { echo "search: emit with $XENV failed ($(tail -1 "$EM3/log")): skipped" >> "$O/log.txt"; XENV=""; return 0; }
  j=$((i + 1)); [ -f "$O/sizes_$j.vh" ] && mv "$O/sizes_$j.vh" "$O/sizes_${j}_unbuilt.vh"
  { cat "$O/sizes_$X.vh"
    grep '^`define' "$EM3/start.vh" | while read -r _ m v _; do
      grep -q "^\`define $m " "$O/sizes_$X.vh" || echo "\`define $m $v   // new line ($XENV, estimate x $SC3)"; done
  } > "$O/sizes_$j.vh"
  echo "search: $XENV from it $j ($(grep -c 'new line' "$O/sizes_$j.vh") new line(s))" >> "$O/log.txt"
  while [ "$k" -lt "$M3" ]; do
    k=$((k + 1))
    build "$j" "$O/sizes_$j.vh" || { echo "search: BUILD FAILED it=$j" >> "$O/log.txt"; break; }
    rule "$j" "$O/sizes_$j.vh" || { echo "search: RULE FAILED it=$j" >> "$O/log.txt"; break; }
    ro=""; [ "$k" -gt $((M3 - 2)) ] && ro="--raise-only --headroom ${AUTO_HEADROOM:-1}"
    st=$(python3 "$T/ratchet.py" "$O/sizes_$j.vh" "$RUNS/ca/${N}_$j/rule/sizes.vh" "$RUNS/ca/${N}_$j/rule/negative_sized.tsv" \
         "$O/sizes_$((j + 1)).vh" "$O/pinned.txt" $ro)
    echo "search it $j $(cat "$O/it_$j.txt") | $(echo "$st" | head -1)${ro:+ ($ro)}" >> "$O/log.txt"
    echo "$st" > "$O/search_ratchet_$j.txt"
    read -r _ nr3 _ _ _ neg3 _ nl3 _ _ <<< "$(echo "$st" | head -1)"
    if [ "$neg3" = 0 ]; then LC3=$j; { [ "$nl3" = 0 ] || [ -n "$ro" ]; } && break; fi
    if [ "$neg3" != 0 ] && [ "$nr3" = 0 ]; then break; fi
    j=$((j + 1))
  done
  if [ -z "$LC3" ]; then
    echo "search: no clean route with $XENV (last it $j): ships ${N}_$X" >> "$O/log.txt"; XENV=""; return 0; fi
  final "$LC3"
  P0=$(grep -o 'P=[0-9]*' "$O/it_$X.txt" | head -1 | cut -d= -f2); P3=$(grep -o 'P=[0-9]*' "$O/it_$LC3.txt" | head -1 | cut -d= -f2)
  echo "search: ${N}_$LC3 ($XENV) P=${P3:-NA} vs ${N}_$X P=${P0:-NA}" >> "$O/log.txt"
  if [ -n "$P3" ] && { [ "$RC" != 0 ] || [ -z "$P0" ] || [ "$P3" -lt "$P0" ]; }; then
    cp "$O/sizes_$LC3.vh" "$O/sizes_final.vh"; echo "$XENV" > "$O/structure.env"
    RES3="CLEAN it=$LC3 route=${N}_$LC3 (last it $j; search $XENV) $(cat "$O/it_$LC3.txt")"; RC=0
  else
    echo "search: ships ${N}_$X (P not lower)" >> "$O/log.txt"; XENV=""
  fi
}
if [ -n "$LC" ]; then
  final "$LC"; cp "$O/sizes_$LC.vh" "$O/sizes_final.vh"; X=$LC; RC=0
  RES3="CLEAN it=$LC route=${N}_$LC (last it $i) $(cat "$O/it_$LC.txt")"
else
  final "$i"; cp "$O/sizes_$i.vh" "$O/sizes_final.vh"; X=$i
  if [ "$nr" = 0 ]; then RC=3
    RES3="NOT CLEAN it=$i: $neg negative, none fixable by a line (route ${N}_$i) $(cat "$O/it_$i.txt")"
  else RC=2
    RES3="NOT CLEAN after $i (last route ${N}_$i; next sizes sizes_$((i + 1)).vh) $(cat "$O/it_$i.txt")"
  fi
fi
[ "${AUTO_SEARCH:-0}" = 1 ] && search_phase
echo "$RES3" | tee -a "$O/result.txt"
exit "$RC"
