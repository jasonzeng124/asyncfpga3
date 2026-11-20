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
# AUTO_FINISH_SEEDS=K (opt-in; unset or 1 = as before): in the finish phase, a route the rule finds NOT clean is drawn
# again from the same sizes on up to K-1 more placer seeds (S + 1000 j, j = 1..K-1, lanes L"s"j, routes NAME_I"s"j, one
# attempt each: a missed bench clock is a failed draw), the rule run on each in turn; the first one it finds clean is
# ADOPTED as route I: its hw / r / ca directories become NAME_I (the seed-S route is kept as NAME_I"s"0), its it / ca /
# rule / neg / lines files become iteration I's, seed_I.txt holds its seed (final() and a resume rebuild exactly it), and
# the loop ships it as it would a clean seed-S route. If none is clean, the loop goes on from the seed-S route, exactly
# as without the knob (the same next sizes, so the same later routes). AUTO_FINISH_JOBS=J builds J of them at once
# (default 1). log.txt gets one "alt it I seed S' ..." line per draw and an "adopt it I ..." line.
# Why (subagent converge, research/data/converge/notes.txt): on the farm's loops 95 % of the rows short on a finish route
# are on constraints and lines no earlier finish route had short (2255 of 2367; on 2 of 383 routes was every short row a
# recurrence), so more headroom on the raised lines (AUTO_HEADROOM, AUTO_NEAR_PS) cannot reach them. On local loops that
# kept every route's corner_audit report, a re-route moves a constraint's margin by sd ~0.5 ns with none of its lines
# changed, and the rows that open on a raise-only route had a median 474 ps the route before; at identical sizes three
# seeds' short sets barely overlap. A finish route is a fresh draw of those margins: this takes more draws per step,
# with no padding, where a slack covering the scatter would pad every line (corner_audit --slack 1000 on xorshift s1's
# route 5: 100 -> 186 kernel delay elements). AUTO_FINISH=N (more raise-only steps) is the other lever; both were run
# locally on farm loops resumed at their finish phase (notes.txt) and at scale by research/cluster/requests/finseeds1.sh.
#
# AUTO_SHIP_LEAST=1 (opt-in; unset = as before: the last route): when no route was clean, the loop ships the LEAST SHORT
# route it built (it >= 1, from neg_I.txt): the smallest total miss (per short constraint its worst corner's deficit,
# summed), then the fewest short constraints, then the later route. result.txt names it ("shipped it=X", which
# research/tools/suite/suite_one.sh reads), with the last route's numbers beside it; final() rebuilds it from sizes_X and
# seed_X if this run did not build it. Why (research/data/converge/notes.txt, asked by the research bot after farm
# ringfuse1 task 31: ipow s7 shipped it 7 with 8 constraints short by up to 1019 ps, where it 6 had two, -84 / -18 ps,
# and it 7 fails draw 10707): each finish route is a fresh draw, so the last one is no better than any other; on 64 of
# the farm's 135 NOT CLEAN loops an earlier finish route had a smaller total miss (median 343 vs 1081 ps).
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
# AUTO_AUTONAME=1 (opt-in; default: AUTO_PLACE_KEEP's value; unset / 0, the builds are what they were): every route of
# the loop is built with BD_AUTONAME=1 (cells/hw/build_bench.sh: yosys autoname, so a cell keeps its name from one
# route to the next, which AUTO_PLACE_KEEP's matching needs; research/data/placekeep/README.md).
ANENV=""; [ "${AUTO_AUTONAME:-${AUTO_PLACE_KEEP:-0}}" = 1 ] && ANENV="BD_AUTONAME=1"
if [ -n "${AUTO_RESUME:-}" ] && [ -f "$AUTO_RESUME/sizes_1.vh" ]; then
  RES=$(cd "$AUTO_RESUME" && pwd)
  [ "$RES" = "$(cd "$O" && pwd)" ] || cp "$RES"/*.txt "$RES"/*.vh "$O/" 2>/dev/null
fi
: > "$O/result.txt"
D=${K}_bench_gen
# AUTO_OVERBUILD=H (opt-in; unset, nothing changes) builds the finish phase's routes long and ships them trimmed, so it
# implies the trim step: a route that is clean only after its trims must not ship untrimmed.
[ -n "${AUTO_OVERBUILD:-}" ] && AUTO_TRIM=1
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
  # CA_FAST=1 (default here since 2026-11-18 23:35 UTC; CA_FAST=0 the old path): corner_audit runs its audits once and
  # forks every per-line sensitivity run from the base (research/tools/ca_fast.py, subagent loopfast): the rule step
  # 8-10x faster (gcd ~34x), every output file byte-identical to the old path on xorshift, collatz, ipow, gather,
  # collatz64, dot2, iterative_sqrt, quadrec routes (research/tools/auto/ca_fast_e2e.sh) and the gcd / isprime it-0
  # proposals equal to the farm's old-rule ones (research/data/loopfast/).
  # BD_RAM_GUARD_PS=400 (default here since 2026-11-19; subagent ifloop, research/data/suite/ifloop.md): rule B (a RAM's
  # setup: the host's or a store's WE / DI against the manufactured clock, sized by bd_mem's USETUP line) had no scatter
  # guard; on if_loop_1 seed 1 it passed the host fill's WE at +79 ps and 2 of 4 draws failed (the draws' within-die
  # scatter moves that race by ~112 ps, one sigma). 400 ps = 3x the largest spread measured on any memory route's worst
  # race. It only lengthens a setup line, which sits outside the kernel's loop on a host access.
  # PYTHONHASHSEED pinned (default 1): the rule iterates Python sets of pin names (find_chains), so the greedy shrink's
  # order among lines of equal length, and with it a proposal, could depend on the hash seed (loopfast, 2026-11-18).
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
  # BD_SKEW_MUXN=1 (default ON in this loop since 2026-11-19 05:47 UTC; BD_SKEW_MUXN= turns it off; research/data/muxsel/notes.txt): rule E also checks every bdc_muxnN's select decode
  # sel[k] = ctl_req & (s == k) (its ctl_req pin against each index pin), which no rule measured, so the select link's DELAY
  # that guards it was "on no measured constraint: kept" (cmpchain: shrunk to 1, runts on the decode outputs in GLS).
  local c; for c in ${AUTO_RULE_CORNERS:-0.20 0.31}; do
    BD_SKEW_MUXN=${BD_SKEW_MUXN-1} BD_SKEW_E_JOIN=${BD_SKEW_E_JOIN:-} BD_SKEW_E_JOIN_DEPTH=${BD_SKEW_E_JOIN_DEPTH:-1} \
    PYTHONHASHSEED=${PYTHONHASHSEED:-1} CA_FAST=${CA_FAST:-1} BD_RAM_GUARD_PS=${BD_RAM_GUARD_PS:-400} \
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
place_dump() {  # place_dump I: route I's placement, one "cell<TAB>bel" per line (AUTO_PLACE_KEEP)
  python3 - "$RUNS/hw/${N}_$1/${D}_routed.json" > "$O/place_$1.txt" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
for m in d["modules"].values():
    cs = m.get("cells", {})
    if any("NEXTPNR_BEL" in c.get("attributes", {}) for c in cs.values()):
        for n, c in sorted(cs.items()):
            b = c.get("attributes", {}).get("NEXTPNR_BEL")
            if b:
                print("%s\t%s" % (n, b))
        break
PY
}
build() {  # build I SIZES: the route and its prjxray SDF only (LANE_NORUN=1); final() runs the full stack on the kept one
  # A route whose BENCH side (the PS-clocked harness, not the kernel) misses build_bench.sh's 83 MHz target is refused
  # by build_bench.sh ("TIMING FAILED"), and with NEXTPNR_SEED pinned it gets one attempt, so one such route used to
  # end the whole loop (farm: quadrec s2 at it 5, varshift s4 at it 3, the stores subagent's fill s1 at it 2). Now
  # that iteration is built again on seed S + 100, then S + 200 (AUTO_SEED_TRIES, default 3 attempts); only a missed
  # bench clock is retried. The seed each iteration was built with is in seed_I.txt (a resume rebuilds with it; a
  # board item names it). Without such a miss nothing changes: every iteration is built on S, as before.
  local i=$1 Z=$2 a s HWI=$RUNS/hw/${N}_$1 PF="" pfa
  local s0; s0=$(cat "$O/seed_$i.txt" 2>/dev/null || echo "$S")
  # AUTO_PLACE_KEEP=1 (opt-in; unset, nothing below changes a build): a FINISH-phase route keeps the placement of the
  # route before it (cells/hw/build_bench.sh BD_PLACE_FROM; only the cells a raised line adds are placed). Why: a
  # fresh re-route moves every margin by ~0.5 ns (sd) where no line changed (research/data/converge/notes.txt), and the
  # raise-only steps chase those fresh misses; test_bool_array s1 it 5 -> 6: 6051 of 6136 cells moved for 3 new LUTs.
  # placefrom_I.txt names the route kept (a rebuild on resume uses it again); place_I.txt is route I's placement
  # (cell, bel), written for every route the loop builds while the knob is on. A bench clock missed with the kept
  # placement is retried fresh on the next seed (and placefrom_I.txt removed), as before.
  # The previous route's routed JSON when it is on this disk (place_from.py's matching needs its connectivity and LUT
  # pins), else its place_J.txt (cell / bel only: a resume elsewhere; names alone match less).
  local j=""
  if [ -f "$O/placefrom_$i.txt" ]; then j=$(cat "$O/placefrom_$i.txt")
  elif [ "${AUTO_PLACE_KEEP:-0}" = 1 ] && [ "${ph:-1}" = 2 ] && [ "$i" -ge 1 ]; then j=$((i - 1)); fi
  if [ -n "$j" ]; then
    [ -f "$O/place_$j.txt" ] || { [ -f "$RUNS/hw/${N}_$j/${D}_routed.json" ] && place_dump "$j"; }
    if [ -f "$RUNS/hw/${N}_$j/${D}_routed.json" ]; then PF=$RUNS/hw/${N}_$j/${D}_routed.json
    elif [ -f "$O/place_$j.txt" ]; then PF=$O/place_$j.txt; fi
    [ -n "$PF" ] && echo "$j" > "$O/placefrom_$i.txt"
  fi
  rm -rf "$HWI" "$RUNS/r/${N}_$i"   # a failed build must not leave an older route's files looking like this one's
  if [ -n "$PF" ]; then   # the kept placement, on the iteration's seed; any failure: built fresh below, as without it
    LANE_NORUN=1 "$LANE" "$L" "${N}_$i" "$K" "$Z" "$s0" "$VEC" BDC_AUTO=1 ${XENV:-} ${ANENV} BD_PLACE_FROM="$PF" > "$O/it_$i.log" 2>&1
    tail -1 "$O/it_$i.log" > "$O/it_$i.txt"
    if [ -f "$RUNS/r/${N}_$i/xray.sdf" ] && [ -f "$HWI/${D}_routed.json" ]; then
      echo "$s0" > "$O/seed_$i.txt"; place_dump "$i"
      echo "it $i: placement kept from it $(cat "$O/placefrom_$i.txt") ($(grep -o 'place_from: bound [0-9]* of [0-9]* cells.*) from' "$HWI/build.log" 2>/dev/null | head -1 | sed 's/ from$//'))" >> "$O/log.txt"
      return 0
    fi
    echo "it $i: the kept placement failed ($(grep -m1 -E 'ERROR|FAILED' "$HWI/build.log" 2>/dev/null | cut -c1-120)); built fresh" >> "$O/log.txt"
    rm -f "$O/placefrom_$i.txt"; rm -rf "$HWI" "$RUNS/r/${N}_$i"
  fi
  for a in $(seq 0 $(( ${AUTO_SEED_TRIES:-3} - 1 ))); do
    s=$s0; [ "$a" -gt 0 ] && s=$((S + 100 * a)); [ "$a" -gt 0 ] && [ "$s" = "$s0" ] && s=$((S + 100 * (a + 1)))
    [ "$a" -gt 0 ] && rm -rf "$HWI" "$RUNS/r/${N}_$i"
    LANE_NORUN=1 "$LANE" "$L" "${N}_$i" "$K" "$Z" "$s" "$VEC" BDC_AUTO=1 ${XENV:-} ${ANENV} > "$O/it_$i.log" 2>&1
    tail -1 "$O/it_$i.log" > "$O/it_$i.txt"
    if [ -f "$RUNS/r/${N}_$i/xray.sdf" ] && [ -f "$HWI/${D}_routed.json" ]; then
      echo "$s" > "$O/seed_$i.txt"; [ "${AUTO_PLACE_KEEP:-0}" = 1 ] && place_dump "$i"
      return 0
    fi
    grep -q "TIMING FAILED" "$HWI/build.log" 2>/dev/null || return 1
    echo "it $i: seed $s missed the bench clock ($(grep -o 'TIMING FAILED: [0-9.]* MHz' "$HWI/build.log" | head -1)); next seed" >> "$O/log.txt"
  done
  return 1
}
mkbit() {  # mkbit HWDIR: the bitstream from HWDIR/D.fasm, as cells/hw/build_bench.sh makes it
  local P=xc7z010clg400-1 DB=${TC:-$HOME/dev2/lib/fpgatoolchain}/openxc7/share/nextpnr/prjxray-db/zynq7
  local PX=${TC:-$HOME/dev2/lib/fpgatoolchain}/openxc7-src/prjxray
  PYTHONPATH="$PX:${TC:-$HOME/dev2/lib/fpgatoolchain}/openxc7/lib/python${PYTHONPATH:+:$PYTHONPATH}" \
    python3 "$PX/utils/fasm2frames.py" --db-root "$DB" --part "$P" "$1/$D.fasm" > "$1/$D.frames" 2> "$1/frames.log" &&
  "${TC:-$HOME/dev2/lib/fpgatoolchain}/openxc7/bin/xc7frames2bit" --part_file "$DB/$P/part.yaml" --part_name "$P" \
    --frm_file "$1/$D.frames" --output_file "$1/$D.bit" > "$1/bit.log" 2>&1
}
neg_keys() {  # neg_keys FILE: "key worst" per short constraint (a rule's neg file), the worst corner's margin
  awk -F'\t' 'NR > 1 && NF >= 3 { if (!($3 in m) || $2 < m[$3]) m[$3] = $2 } END { for (k in m) print k "\t" m[k] }' "$1" 2>/dev/null | sort
}
trim_record() {  # trim_record SIZES RECORD LOG: trim_lines.py's moves into the effective sizes and the MACRO=LEN record
  python3 - "$1" "$2" "$3" <<'PY'
import re, sys
cur, rec, log = sys.argv[1:4]
got = {}
for l in open(log):
    m = re.match(r"trim (\S+) \S+: (\d+) -> (\d+)", l)
    if m:
        got.setdefault(m.group(1), set()).add(int(m.group(3)))
refused = {m.group(1) for m in (re.match(r"REFUSED (\S+?):", l) for l in open(log)) if m}
new = {k: v.pop() for k, v in got.items() if len(v) == 1 and k not in refused}
lines = open(cur).read().splitlines()
out = []
for l in lines:
    m = re.match(r"`define\s+(\S+)\s+(\d+)", l)
    out.append("`define %s %d" % (m.group(1), new[m.group(1)]) if m and m.group(1) in new else l)
open(cur, "w").write("\n".join(out) + "\n")
r = {}
for l in open(rec).read().split():
    a, b = l.split("="); r[a] = b
for k, v in new.items():
    r[k] = str(v)
open(rec, "w").write("".join("%s=%s\n" % kv for kv in sorted(r.items())))
PY
}
trim_route() {  # trim_route I (AUTO_TRIM=1): the shipped route's lines shortened to what THIS route needs, by LUT INIT only
  # research/data/trim/README.md: a line of LUT2 elements can be made any length 1..N after routing (trim_lines.py),
  # so the rule's proposal on the route itself is applied with no re-place and no re-route, and checked on the same
  # route (the rule reads trimmed lines). Each step: rule -> proposal -> trim every line it moves (shorter, or longer
  # within the line's built length) -> bits -> rule; a step whose short constraints include one the route did not have
  # before, or whose total miss is larger, is reverted (keeping the lines those rows do not depend on, once per step).
  # AUTO_TRIM_MAX steps (default 6). The proposal is the rule's trim mode (AUTO_TRIM_PLAN=ca, see below): exact per
  # entry, so a step normally opens nothing. With AUTO_TRIM_PLAN=0, AUTO_TRIM_DAMP=1 (default) shortens each line by half
  # its gap to the rebuild proposal (at least one element), because that proposal prices a removed element at the
  # line's mean step while a trimmed line is entered through the side net and loses more (xorshift s1 it 9: the full
  # proposal opened 16 short constraints, 1458 ps, once the rule read trimmed lines correctly).
  # $O/trim_I.txt records the final MACRO=LEN; a rebuild of route I (resume, a board item) re-applies it.
  local i=$1 H=$RUNS/hw/${N}_$1 k Z cur prev_keys prev_tot keys tot t retried="" CA_LAST=""
  [ -f "$H/${D}_routed.json" ] || return 0
  if [ ! -f "$H/${D}_routed.untrimmed.json" ]; then
    cp "$H/${D}_routed.json" "$H/${D}_routed.untrimmed.json"; cp "$H/$D.fasm" "$H/$D.untrimmed.fasm"; cp "$H/$D.bit" "$H/$D.untrimmed.bit"
  fi
  if [ -z "${TRIM_CONTINUE:-}" ] && [ -f "$O/trim_$i.txt" ] && [ -s "$O/trim_$i.txt" ]; then   # a rebuild: re-apply the recorded trims
    python3 "$T/trim_lines.py" --partial "$H/${D}_routed.untrimmed.json" "$H/$D.untrimmed.fasm" "$H/${D}_routed.json" "$H/$D.fasm" \
      $(cat "$O/trim_$i.txt") > "$O/trim_${i}_reapply.log" 2>&1 && mkbit "$H"
    echo "trim: it $i re-applied $(wc -l < "$O/trim_$i.txt") recorded trim(s)" >> "$O/log.txt"; return 0
  fi
  cur=$O/sizes_${i}_trim.vh
  if [ -z "${TRIM_CONTINUE:-}" ]; then cp "$O/sizes_$i.vh" "$cur"; : > "$O/trim_$i.txt"; fi   # TRIM_CONTINUE: from the trims made
  prev_keys=""; prev_tot=""
  for k in $(seq 1 $(( ${AUTO_TRIM_MAX:-6} + 2 ))); do   # past AUTO_TRIM_MAX a pass only checks (a partial retry may need one)
    rm -rf "$RUNS/hw/${N}_${i}t$k" "$RUNS/r/${N}_${i}t$k"
    ln -s "$H" "$RUNS/hw/${N}_${i}t$k"; ln -s "$RUNS/r/${N}_$i" "$RUNS/r/${N}_${i}t$k"
    if [ "${AUTO_TRIM_PLAN:-ca}" = ca ]; then CA_TRIM=1 rule "${i}t$k" "$cur"; else rule "${i}t$k" "$cur"; fi ||
      { echo "trim: it $i step $k: RULE FAILED" >> "$O/log.txt"; break; }
    CA_LAST=$RUNS/ca/${N}_${i}t$k
    keys=$(neg_keys "$O/neg_${i}t$k.txt" | cut -f1); tot=$(neg_keys "$O/neg_${i}t$k.txt" | awk -F'\t' '{s -= $2} END {print s + 0}')
    if [ -n "$prev_tot" ]; then   # the step before was applied: did it open anything?
      local newk; newk=$(comm -13 <(echo "$prev_keys") <(echo "$keys") | grep .)
      if [ -n "$newk" ] || [ "$tot" -gt "$prev_tot" ]; then
        cp "$H/${D}_routed.prev.json" "$H/${D}_routed.json"; cp "$H/$D.prev.fasm" "$H/$D.fasm"; cp "$H/$D.prev.bit" "$H/$D.bit"
        cp "$O/sizes_${i}_trim.prev.vh" "$cur"; cp "$O/trim_${i}.prev.txt" "$O/trim_$i.txt"
        # once per step: keep the trims of every line the newly short constraints do not depend on (each row's
        # "depends on" in the rule's report), and try again; else the whole step stays reverted
        local tred=""
        if [ -z "$retried" ] && [ -n "$newk" ]; then
          tred=$(python3 - "$t" "$CA_LAST" <<'PY'
import re, sys
step = dict(x.split("=") for x in sys.argv[1].split())
labels = set()
for k in sys.stdin.read().split("\n"):
    if k.strip():
        labels.add(k.split()[1] if len(k.split()) > 1 else k)
deps = set()
for c in ("0.20", "0.31"):
    try:
        lines = open("%s/rule_%s/report.txt" % (sys.argv[2], c)).read().splitlines()
    except OSError:
        continue
    for j, l in enumerate(lines):
        f = l.split()
        if len(f) >= 3 and f[2] in labels and j + 1 < len(lines) and "depends on:" in lines[j + 1]:
            deps |= {"BD_SZ_" + m.group(1) for m in re.finditer(r"(\w+)\(-", lines[j + 1])}
keep = {k: v for k, v in step.items() if k not in deps}
print(" ".join("%s=%s" % kv for kv in sorted(keep.items())) if keep and len(keep) < len(step) else "")
PY
<<< "$newk")
        fi
        if [ -n "$tred" ]; then
          retried=1; t=$tred
          python3 "$T/trim_lines.py" --partial "$H/${D}_routed.prev.json" "$H/$D.prev.fasm" "$H/${D}_routed.json" "$H/$D.fasm" $t \
            > "$O/trim_${i}_${k}r.log" 2>&1 && mkbit "$H" || { echo "trim: it $i: partial retry FAILED" >> "$O/log.txt"; break; }
          trim_record "$cur" "$O/trim_$i.txt" "$O/trim_${i}_${k}r.log"
          echo "trim: it $i step $((k - 1)) opened $(echo "$newk" | grep -c .) constraint(s): kept $(echo $t | wc -w) of its line(s), the rest reverted" >> "$O/log.txt"
          continue
        fi
        echo "trim: it $i step $((k - 1)) reverted (short: $(echo $keys | wc -w) constraint(s), $tot ps; before: $prev_tot ps)" >> "$O/log.txt"
        keys=$prev_keys; tot=$prev_tot   # the state left applied is the step before
        break
      fi
    fi
    retried=""
    prev_keys=$keys; prev_tot=$tot
    [ "$k" -gt "${AUTO_TRIM_MAX:-6}" ] && { echo "trim: it $i: $(echo $keys | wc -w) short, $tot ps after the last step" >> "$O/log.txt"; break; }
    # the trims. AUTO_TRIM_PLAN=ca (default): the rule's own proposal made in its trim mode (corner_audit CA_TRIM=1:
    # each line priced at its new entry exactly -- input wire, the anchor the entry skips, the chain after it -- and
    # verified with the entry moved in the timing graph as trim_lines.py moves it; on xorshift s1 it 9 every margin
    # it predicted matched the trimmed route's within 2 ps), applied in full. AUTO_TRIM_PLAN=1: trim_plan.py (a linear
    # charge; it opened 12 constraints there). AUTO_TRIM_PLAN=0: the rule's rebuild proposal, damped (opened 14-16).
    if [ "${AUTO_TRIM_PLAN:-ca}" = ca ]; then
      t=$(python3 - "$cur" "$O/rule_${i}t$k.vh" <<'PY'
import re, sys
rd = lambda p: {m.group(1): int(m.group(2)) for m in (re.match(r"`define\s+(\S+)\s+(\d+)", l) for l in open(p)) if m}
a, b = rd(sys.argv[1]), rd(sys.argv[2])
print(" ".join("%s=%d" % (k, v) for k, v in sorted(b.items()) if k in a and v != a[k]))
PY
)
    elif [ "${AUTO_TRIM_PLAN:-ca}" = 1 ]; then
      t=$(python3 "$T/trim_plan.py" "$CA_LAST" "$H/${D}_routed.json" 2> "$O/trim_${i}_${k}_plan.txt")
    else
    t=$(python3 - "$cur" "$O/rule_${i}t$k.vh" "${AUTO_TRIM_DAMP:-1}" <<'PY'
import re, sys
rd = lambda p: {m.group(1): int(m.group(2)) for m in (re.match(r"`define\s+(\S+)\s+(\d+)", l) for l in open(p)) if m}
a, b = rd(sys.argv[1]), rd(sys.argv[2])
damp = sys.argv[3] == "1"     # AUTO_TRIM_DAMP: a shortening moves half the gap (at least one element); a raise, all
out = []
for k, v in sorted(b.items()):
    if k in a and v != a[k]:
        if damp and v < a[k]:
            v = a[k] - max(1, (a[k] - v + 1) // 2)
        out.append("%s=%d" % (k, v))
print(" ".join(out))
PY
)
    fi
    # TRIM_ALLOW=FILE (AUTO_TRIM_SCOPE=cycle): only the lines listed there may move (the critical cycle's, cycle_macros.py)
    if [ -n "${TRIM_ALLOW:-}" ] && [ -n "$t" ]; then
      t=$(for x in $t; do grep -qxF "${x%%=*}" "$TRIM_ALLOW" && echo "$x"; done | tr '\n' ' ' | sed 's/ $//')
    fi
    [ -n "$t" ] || { echo "trim: it $i step $k: the rule moves no line$([ -n "${TRIM_ALLOW:-}" ] && echo ' on the critical cycle') ($(echo $keys | wc -w) short, $tot ps)" >> "$O/log.txt"; break; }
    cp "$H/${D}_routed.json" "$H/${D}_routed.prev.json"; cp "$H/$D.fasm" "$H/$D.prev.fasm"; cp "$H/$D.bit" "$H/$D.prev.bit"
    cp "$cur" "$O/sizes_${i}_trim.prev.vh"; cp "$O/trim_$i.txt" "$O/trim_${i}.prev.txt"
    python3 "$T/trim_lines.py" --partial "$H/${D}_routed.prev.json" "$H/$D.prev.fasm" "$H/${D}_routed.json" "$H/$D.fasm" $t \
      > "$O/trim_${i}_$k.log" 2>&1 || { echo "trim: it $i step $k: trim_lines FAILED" >> "$O/log.txt"; break; }
    mkbit "$H" || { echo "trim: it $i step $k: bitstream FAILED" >> "$O/log.txt"
      cp "$H/${D}_routed.prev.json" "$H/${D}_routed.json"; cp "$H/$D.prev.fasm" "$H/$D.fasm"; cp "$H/$D.prev.bit" "$H/$D.bit"; break; }
    trim_record "$cur" "$O/trim_$i.txt" "$O/trim_${i}_$k.log"
    echo "trim: it $i step $k: $(grep -c '^trim ' "$O/trim_${i}_$k.log") chain(s) moved, $(grep -c '^REFUSED' "$O/trim_${i}_$k.log") refused (before: $(echo $keys | wc -w) short, $tot ps)" >> "$O/log.txt"
  done
  # the state left applied: its short constraints and total miss (trim_check reads it); -1 if no rule ran
  if [ -n "$prev_tot" ]; then echo "$(echo $keys | wc -w) $tot" > "$O/trim_${i}_final.txt"; else echo "-1 -1" > "$O/trim_${i}_final.txt"; fi
}
trim_check() {  # trim_check I (AUTO_OVERBUILD, finish phase): 0 if route I is made rule-clean by trims alone (the trim
  # step run on it now: the rule's trim mode, every step verified); the route's bits are then put back untrimmed and the
  # trims kept in trim_I.txt, which final() re-applies when the loop ships route I.  1 otherwise (trims kept recorded).
  local i=$1 H=$RUNS/hw/${N}_$1 n
  trim_route "$i"
  n=$(awk '{print $1}' "$O/trim_${i}_final.txt" 2>/dev/null)
  if [ -f "$H/${D}_routed.untrimmed.json" ]; then
    cp "$H/${D}_routed.untrimmed.json" "$H/${D}_routed.json"; cp "$H/$D.untrimmed.fasm" "$H/$D.fasm"; cp "$H/$D.untrimmed.bit" "$H/$D.bit"
  fi
  echo "it $i trim check: ${n:-?} short after the trim step ($(grep -c . "$O/trim_$i.txt" 2>/dev/null) line(s) trimmed)" >> "$O/log.txt"
  [ "${n:-1}" = 0 ]
}
overbuild_args() {  # overbuild_args I: AUTO_OVERBUILD=H (opt-in): at the switch to the finish phase every trimmable line
  # of route I (trim_lines.py --list) is built H elements longer than max(sizes, proposal); see ratchet.py --overbuild
  [ -n "${AUTO_OVERBUILD:-}" ] || return 0
  python3 "$T/trim_lines.py" --list "$RUNS/hw/${N}_$1/${D}_routed.json" > "$O/trimmable_$1.txt" 2>/dev/null || return 0
  echo "--overbuild $AUTO_OVERBUILD $O/trimmable_$1.txt"
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
  if [ "${AUTO_TRIM:-0}" = 1 ]; then
    # AUTO_TRIM_P0 (default 1 when AUTO_TRIM=1): the untrimmed route's own full stack first (it_I_untrimmed.txt: its P,
    # its bits verdict), so every trimmed route carries its own paired before / after.  AUTO_TRIM_ONLY has the loop's.
    if [ ! -f "$O/it_${i}_untrimmed.txt" ] && [ "${AUTO_TRIM_P0:-1}" = 1 ]; then
      "$R/research/tools/fifteen/lane2_run.sh" "${N}_$i" "$K" "$VEC" BDC_AUTO=1 ${XENV:-} > "$O/final_${i}_untrimmed.log" 2>&1
      tail -1 "$O/final_${i}_untrimmed.log" > "$O/it_${i}_untrimmed.txt"
      echo "final it $i untrimmed $(cat "$O/it_${i}_untrimmed.txt")" >> "$O/log.txt"
      # where the untrimmed route's critical cycle goes (chain / wire between cells / cell logic, per instance)
      python3 "$R/research/tools/eventgraph/cycdecomp.py" "$R/research/data/eventgraph/graphs/${N}_$i" > "$O/cyc_${i}_untrimmed.txt" 2>&1
    fi
    if [ "${AUTO_TRIM_SCOPE:-all}" = cycle ]; then
      # AUTO_TRIM_SCOPE=cycle (opt-in, 2026-11-20; formal B25): trim only the lines of instances on the critical cycle
      # (cycdecomp of the route as it stands), then re-time the trimmed route and let the NEW critical cycle's lines move
      # too, up to AUTO_TRIM_ROUNDS rounds (default 3), until the cycle brings no new line.  A line off every cycle the
      # trims expose keeps its built length: shortening it cannot lower the period and spends a race's margin.
      local r rr
      python3 "$T/cycle_macros.py" "$O/cyc_${i}_untrimmed.txt" "$O/sizes_$i.vh" > "$O/trim_allow_$i.txt"
      echo "trim: it $i scope cycle, round 1: $(grep -c . "$O/trim_allow_$i.txt") line(s) on the untrimmed cycle" >> "$O/log.txt"
      TRIM_ALLOW=$O/trim_allow_$i.txt trim_route "$i"
      for r in $(seq 2 "${AUTO_TRIM_ROUNDS:-3}"); do
        [ -s "$O/trim_$i.txt" ] || break       # nothing trimmed: the cycle is the untrimmed one
        "$R/research/tools/fifteen/lane2_run.sh" "${N}_$i" "$K" "$VEC" BDC_AUTO=1 ${XENV:-} > "$O/final_${i}_r$r.log" 2>&1
        python3 "$R/research/tools/eventgraph/cycdecomp.py" "$R/research/data/eventgraph/graphs/${N}_$i" > "$O/cyc_${i}_r$r.txt" 2>&1
        echo "trim: it $i round $r: $(tail -1 "$O/final_${i}_r$r.log" | grep -o 'P=[0-9A-Z]*')" >> "$O/log.txt"
        rr=$(python3 "$T/cycle_macros.py" "$O/cyc_${i}_r$r.txt" "$O/sizes_$i.vh" | grep -vxF -f "$O/trim_allow_$i.txt")
        [ -n "$rr" ] || { echo "trim: it $i round $r: the cycle brings no new line" >> "$O/log.txt"; break; }
        echo "$rr" >> "$O/trim_allow_$i.txt"
        echo "trim: it $i round $r: $(echo "$rr" | grep -c .) new line(s) on the cycle" >> "$O/log.txt"
        TRIM_ALLOW=$O/trim_allow_$i.txt TRIM_CONTINUE=1 trim_route "$i"
      done
    else
      trim_route "$i"
    fi
  fi
  "$R/research/tools/fifteen/lane2_run.sh" "${N}_$i" "$K" "$VEC" BDC_AUTO=1 ${XENV:-} > "$O/final_$i.log" 2>&1
  [ "${AUTO_TRIM:-0}" = 1 ] && python3 "$R/research/tools/eventgraph/cycdecomp.py" "$R/research/data/eventgraph/graphs/${N}_$i" > "$O/cyc_$i.txt" 2>&1
  tail -1 "$O/final_$i.log" > "$O/it_$i.txt"
  echo "final it $i $(cat "$O/it_$i.txt")" >> "$O/log.txt"
}
nneg() {  # nneg DIR: the rule's negative rows on a route (auto_size's clean test: none)
  tail -n +2 "$1/negative_sized.tsv" 2>/dev/null | grep -c .
}
alt_build() {  # alt_build I J SEED (AUTO_FINISH_SEEDS): sizes_I on SEED as route N_IsJ in lane LsJ; one attempt
  local NA=${N}_$1s$2
  rm -rf "$RUNS/hw/$NA" "$RUNS/r/$NA"
  LANE_NORUN=1 "$LANE" "${L}s$2" "$NA" "$K" "$O/sizes_$1.vh" "$3" "$VEC" BDC_AUTO=1 ${XENV:-} ${ANENV} > "$O/it_$1s$2.log" 2>&1
  tail -1 "$O/it_$1s$2.log" > "$O/it_$1s$2.txt"
}
adopt() {  # adopt I J SEED (AUTO_FINISH_SEEDS): route N_IsJ becomes route N_I; the seed-S route is kept as N_Is0
  local i=$1 j=$2 d f c
  for d in hw r ca; do
    rm -rf "$RUNS/$d/${N}_${i}s0"
    [ -e "$RUNS/$d/${N}_$i" ] && mv "$RUNS/$d/${N}_$i" "$RUNS/$d/${N}_${i}s0"
    mv "$RUNS/$d/${N}_${i}s$j" "$RUNS/$d/${N}_$i"
  done
  for d in "${i}s0" "$i"; do   # the rule's links into its route, renamed with it
    [ -d "$RUNS/ca/${N}_$d/seed1/pnr" ] || continue
    ln -sfn "$RUNS/r/${N}_$d/xray.sdf" "$RUNS/ca/${N}_$d/seed1/pnr/soak_xray.sdf"
    ln -sfn "$RUNS/hw/${N}_$d/${D}_routed.json" "$RUNS/ca/${N}_$d/seed1/pnr/soak_routed.json"
  done
  for f in it_$i.txt it_$i.log seed_$i.txt ca_$i.txt rule_$i.vh neg_$i.txt; do
    [ -f "$O/$f" ] && mv "$O/$f" "$O/${f/_$i./_${i}s0.}"
  done
  for c in ${AUTO_RULE_CORNERS:-0.20 0.31}; do
    for f in ca lines; do [ -f "$O/${f}_${i}_$c.txt" ] && mv "$O/${f}_${i}_$c.txt" "$O/${f}_${i}s0_$c.txt"
      cp "$O/${f}_${i}s${j}_$c.txt" "$O/${f}_${i}_$c.txt" 2>/dev/null; done
  done
  for f in it_$i.txt it_$i.log ca_$i.txt rule_$i.vh neg_$i.txt; do cp "$O/${f/_$i./_${i}s$j.}" "$O/$f" 2>/dev/null; done
  sed -i "1s/^${N}_${i}s$j /${N}_$i /" "$O/it_$i.txt"   # lane2's line names the route as it now is
  echo "$3" > "$O/seed_$i.txt"
  echo "adopt it $i seed $3: route ${N}_${i}s$j is ${N}_$i (the seed-$S route kept as ${N}_${i}s0)" >> "$O/log.txt"
}
least_short() {  # least_short LAST (AUTO_SHIP_LEAST): "I TOTAL_PS N" of the least short route it 1..LAST built (neg_I.txt)
  python3 - "$O" "$1" <<'PY'
import os, sys
O, last = sys.argv[1], int(sys.argv[2])
best = None
for i in range(1, last + 1):
    p = os.path.join(O, "neg_%d.txt" % i)
    if not os.path.exists(p):
        continue
    d = {}
    for ln in open(p):
        f = ln.rstrip("\n").split("\t")
        if len(f) >= 3 and f[0] != "rule":
            d[f[2]] = min(d.get(f[2], 0), int(f[1]))
    key = (-sum(d.values()), len(d), -i)
    if best is None or key < best:
        best = key
print("%d %d %d" % (-best[2], best[0], best[1]) if best else "%d -1 -1" % last)
PY
}
least_short_one() {  # least_short_one I: "I TOTAL_PS N" of route I alone
  python3 - "$O/neg_$1.txt" "$1" <<'PY'
import os, sys
d = {}
if os.path.exists(sys.argv[1]):
    for ln in open(sys.argv[1]):
        f = ln.rstrip("\n").split("\t")
        if len(f) >= 3 and f[0] != "rule":
            d[f[2]] = min(d.get(f[2], 0), int(f[1]))
print("%s %d %d" % (sys.argv[2], -sum(d.values()), len(d)))
PY
}
finish_draws() {  # finish_draws I (AUTO_FINISH_SEEDS, finish phase): route I not clean -> sizes_I on more seeds
  local i=$1 j=1 k s n b
  [ "$(nneg "$RUNS/ca/${N}_$i/rule")" -gt 0 ] || return 0
  while [ "$j" -lt "$AUTO_FINISH_SEEDS" ]; do
    b=""; while [ "$(echo $b | wc -w)" -lt "${AUTO_FINISH_JOBS:-1}" ] && [ "$j" -lt "$AUTO_FINISH_SEEDS" ]; do b="$b $j"; j=$((j + 1)); done
    for k in $b; do alt_build "$i" "$k" $((S + 1000 * k)) & done; wait
    for k in $b; do
      s=$((S + 1000 * k))
      if [ ! -f "$RUNS/r/${N}_${i}s$k/xray.sdf" ] || [ ! -f "$RUNS/hw/${N}_${i}s$k/${D}_routed.json" ]; then
        echo "alt it $i seed $s: no route ($(cat "$O/it_${i}s$k.txt" 2>/dev/null))" >> "$O/log.txt"; continue; fi
      rule "${i}s$k" "$O/sizes_$i.vh" || { echo "alt it $i seed $s: RULE FAILED" >> "$O/log.txt"; continue; }
      n=$(nneg "$RUNS/ca/${N}_${i}s$k/rule")
      echo "alt it $i seed $s $(cat "$O/it_${i}s$k.txt") | negative $n" >> "$O/log.txt"
      if [ "$n" = 0 ]; then adopt "$i" "$k" "$s"; return 0; fi
    done
  done
}
# AUTO_TRIM_ONLY=1 (opt-in, with AUTO_RESUME=DIR holding a FINISHED loop's files, e.g. a farm task's auto/; unset, nothing
# here runs): no loop and no search -- the route that loop shipped (its result.txt: "CLEAN it=I", "shipped it=I", else the
# last route) is rebuilt from its own sizes, seed and structure (structure.env when the search phase shipped it), checked
# to be the same route (its sdf md5 against the loop's it_I.txt; a different route stops here), then trimmed exactly as
# the flow's AUTO_TRIM=1 step trims a route it ships (trim_route, the rule's trim mode by default) and given the full
# stack.  result.txt gets the loop's own line back, so suite_one.sh judges route I, now trimmed, on the same draw points
# the loop's own run used: a paired measurement of the trim step, the route itself unchanged.  it_I_untrimmed.txt keeps
# the loop's stack line.  Why: research/data/trim/README.md -- a trim changes LUT INITs only, so its effect can be measured
# on routes the farm already built and judged, without a re-route's scatter (hundreds of ps) in the comparison.
if [ "${AUTO_TRIM_ONLY:-0}" = 1 ]; then
  [ -n "$RES" ] && [ -f "$RES/result.txt" ] || { echo "TRIM-ONLY FAILED (AUTO_RESUME=DIR with a finished loop's files needed)" | tee -a "$O/result.txt"; exit 1; }
  last=$(grep -E '^(CLEAN|NOT CLEAN)' "$RES/result.txt" | tail -1)
  [ -n "$last" ] || { echo "TRIM-ONLY FAILED (no finished loop in $RES)" | tee -a "$O/result.txt"; exit 1; }
  X=$(echo "$last" | grep -o 'shipped it=[0-9]*' | head -1 | cut -d= -f2)
  [ -n "$X" ] || X=$(echo "$last" | sed -n 's/^CLEAN it=\([0-9]*\).*/\1/p')
  [ -n "$X" ] || X=$(echo "$last" | sed -n 's/^NOT CLEAN after \([0-9]*\).*/\1/p')
  [ -n "$X" ] || X=$(echo "$last" | sed -n 's/^NOT CLEAN it=\([0-9]*\).*/\1/p')
  [ -n "$X" ] && [ -f "$O/sizes_$X.vh" ] || { echo "TRIM-ONLY FAILED (no shipped iteration / sizes_$X.vh in $RES)" | tee -a "$O/result.txt"; exit 1; }
  if echo "$last" | grep -q '; search '; then   # the search phase's structure: structure.env, else the line itself
    # (a farm task returns only *.txt / *.vh, so structure.env does not come back; the line says "(last it J; search ENV)")
    if [ -f "$O/structure.env" ]; then XENV=$(cat "$O/structure.env"); else XENV=$(echo "$last" | sed -n 's/.*; search \([^)]*\)).*/\1/p'); fi
  fi
  echo "auto_size $N TRIM-ONLY it $X from $RES ${XENV:+($XENV) }$(date -u +%FT%TZ) head $(git -C "$R" rev-parse --short HEAD)" >> "$O/log.txt"
  cp "$O/it_$X.txt" "$O/it_${X}_untrimmed.txt"
  want=$(awk '{print $2}' "$O/it_${X}_untrimmed.txt")
  build "$X" "$O/sizes_$X.vh" || { echo "TRIM-ONLY FAILED (rebuild of it $X)" | tee -a "$O/result.txt"; exit 1; }
  got=$(awk '{print $2}' "$O/it_$X.txt")
  if [ "$got" != "$want" ]; then
    echo "trim-only: route ${N}_$X rebuilt as sdf $got, the loop's was $want -- DIFFERENT ROUTE, not trimmed" >> "$O/log.txt"
    echo "TRIM-ONLY FAILED (DIFFERENT ROUTE: sdf $got, the loop's $want)" | tee -a "$O/result.txt"; exit 1
  fi
  echo "trim-only: route ${N}_$X rebuilt, sdf $got (the loop's)" >> "$O/log.txt"
  AUTO_TRIM=1 final "$X"
  echo "$last" | tee -a "$O/result.txt"
  exit 0
fi
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
# The finish phase's budget is 6 routes since 2026-11-19 (was 3; subagent converge, research/data/converge/notes.txt):
# a re-route moves every margin by ~0.5 ns (sd), and 95 % of the rows short on a finish route were not short before, so
# only more raise-only routes on the loop's own seed help -- one more made 4 of 5 low-row loops clean. AUTO_FINISH=3 is
# the old budget.
LC=""; FIN=${AUTO_FINISH:-6}
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
           "$O/sizes_$((i + 1)).vh" "$O/pinned.txt" --raise-only --headroom "${AUTO_HEADROOM:-1}" $(near_args "$i") $(overbuild_args "$i") > /dev/null
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
  # AUTO_FINISH_SEEDS (opt-in): a finish route that is not clean is drawn again on more seeds; a clean one is adopted
  [ "$ph" = 2 ] && [ "${AUTO_FINISH_SEEDS:-1}" -gt 1 ] && finish_draws "$i"
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
  # AUTO_OVERBUILD (opt-in; needs AUTO_TRIM=1 to ship the trims): a finish route the rule finds short as built is clean
  # if the trim step alone makes it so (the trims are recorded; final() applies them to the route it ships)
  if [ "$neg" != 0 ] && [ "$ph" = 2 ] && [ -n "${AUTO_OVERBUILD:-}" ] && trim_check "$i"; then
    neg=0; echo "it $i clean after the trim step (AUTO_OVERBUILD)" >> "$O/log.txt"
  fi
  brk=""
  if [ "$neg" = 0 ]; then LC=$i; { [ "$nl" = 0 ] || [ "$ph" = 2 ]; } && brk=1; fi   # clean: done, or go on while it shortens
  if [ -z "$brk" ] && [ "$neg" != 0 ] && [ "$nr" = 0 ]; then brk=1; fi        # negative and nothing the rule can lengthen
  if [ -z "$brk" ] && [ "$ph" = 1 ] && [ "$i" -ge "$MAXIT" ]; then
    if [ -n "$LC" ] || [ "$FIN" -le 0 ]; then brk=1
    else
      ph=2; IMAX=$((MAXIT + FIN))
      # the next sizes without the lowering phase 1's last ratchet did
      python3 "$T/ratchet.py" "$O/sizes_$i.vh" "$RUNS/ca/${N}_$i/rule/sizes.vh" "$RUNS/ca/${N}_$i/rule/negative_sized.tsv" \
         "$O/sizes_$((i + 1)).vh" "$O/pinned.txt" --raise-only --headroom "${AUTO_HEADROOM:-1}" $(near_args "$i") $(overbuild_args "$i") > /dev/null
      echo "phase 2 (raise-only) from it $((i + 1))${AUTO_OVERBUILD:+ (overbuild +$AUTO_OVERBUILD on trimmable lines)}" >> "$O/log.txt"
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
# emit.py's estimate x AUTO_START_SCALE) for at most AUTO_SEARCH_MAXIT routes (default 4), RAISE-ONLY with one element
# of headroom (phase 2's step): the shipped sizes were clean on the old structure, the new stage only adds storage, and
# on xorshift the first route with p8 was 1-3 rows short of the rule (seeds 1 / 3 / 4) at P 17.02 / 18.87 / 15.84 ns
# (v6: 19.80 / 22.47 / 19.43).  AUTO_SEARCH_RESIZE=1 instead re-sizes the new structure as the loop does (pins EMPTY,
# a no-pin recalibration first, then the pinning ratchet, the last two raise-only; at most 6 routes by default): it
# lowered UCMPI1 14 -> 8 on seed 3 but did not settle (seed 1: 1, 9, 23 rows short on its first three routes; seed 4:
# 3, 9, 47), the oscillation research/tools/auto's loop already has.  The last clean route gets the full stack; the
# flow ships it if its measured P is below the first route's (or the first was not clean); else the first route, as
# without the search.  log.txt has both.
search_phase() {
  local G=$R/research/data/eventgraph/graphs/${N}_$X EM3=$O/emit3 k=0 j LC3="" ro st nr3 neg3 nl3 P0 P3
  local RS=${AUTO_SEARCH_RESIZE:-0}; local M3=${AUTO_SEARCH_MAXIT:-$([ "$RS" = 1 ] && echo 6 || echo 4)} SC3=${AUTO_START_SCALE:-0.3} ONLY3=${AUTO_START_ONLY:-'^(?!.*_UMEM[0-9]+_(USETUP|UCO)$)'}
  if ! grep -q "period P = [0-9]" "$G/check.txt" 2>/dev/null; then
    echo "search: no event graph for route ${N}_$X: skipped" >> "$O/log.txt"; return 0; fi
  # AUTO_SEARCH_ARGS (default --depth-only): the search's candidates. "--all-sites --buildable-only --wire 1000" adds a
  # latch on any fork output and on any merge output / result branch (search.py --all-sites, subagent graphsearch:
  # research/data/eventgraph/search_all.md); its ENV names every link of each knob it sets, rules F / M's included.
  python3 "$R/research/tools/eventgraph/search.py" "$G" "$O/sizes_$X.vh" ${AUTO_SEARCH_ARGS:---all-sites --buildable-only --wire 1000} \
    > "$O/search.txt" 2>&1
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
  echo "search: $XENV from it $j ($(grep -c 'new line' "$O/sizes_$j.vh") new line(s))$([ "$RS" = 1 ] && echo '; pins reset' || echo '; raise-only')" >> "$O/log.txt"
  if [ "$RS" = 1 ]; then cp "$O/pinned.txt" "$O/pinned_before_search.txt" 2>/dev/null; : > "$O/pinned.txt"; fi
  while [ "$k" -lt "$M3" ]; do
    k=$((k + 1))
    build "$j" "$O/sizes_$j.vh" || { echo "search: BUILD FAILED it=$j" >> "$O/log.txt"; break; }
    rule "$j" "$O/sizes_$j.vh" || { echo "search: RULE FAILED it=$j" >> "$O/log.txt"; break; }
    ro="--raise-only --headroom ${AUTO_HEADROOM:-1}"
    if [ "$RS" = 1 ]; then ro=""; [ "$k" = 1 ] && ro="--nopin"; [ "$k" -gt $((M3 - 2)) ] && ro="--raise-only --headroom ${AUTO_HEADROOM:-1}"; fi
    st=$(python3 "$T/ratchet.py" "$O/sizes_$j.vh" "$RUNS/ca/${N}_$j/rule/sizes.vh" "$RUNS/ca/${N}_$j/rule/negative_sized.tsv" \
         "$O/sizes_$((j + 1)).vh" "$O/pinned.txt" $ro)
    echo "search it $j $(cat "$O/it_$j.txt") | $(echo "$st" | head -1)${ro:+ ($ro)}" >> "$O/log.txt"
    echo "$st" > "$O/search_ratchet_$j.txt"
    read -r _ nr3 _ _ _ neg3 _ nl3 _ _ <<< "$(echo "$st" | head -1)"
    if [ "$neg3" = 0 ]; then LC3=$j; { [ "$nl3" = 0 ] || [ "${ro#--raise}" != "$ro" ]; } && break; fi
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
  X=$i; SH=""
  if [ "${AUTO_SHIP_LEAST:-1}" = 1 ]; then   # the least short route, not the last (default since 2026-11-19; =0 the last)
    read -r X tm nk <<< "$(least_short "$i")"; read -r _ tl kl <<< "$(least_short_one "$i")"
    SH="; shipped it=$X, the least short: $tm ps over $nk constraint(s) (last route: $tl ps over $kl)"
    echo "least short: it $X ($tm ps over $nk constraint(s)); last it $i ($tl ps over $kl)" >> "$O/log.txt"
  fi
  final "$X"; cp "$O/sizes_$X.vh" "$O/sizes_final.vh"
  if [ "$nr" = 0 ]; then RC=3
    RES3="NOT CLEAN it=$i: $neg negative, none fixable by a line (route ${N}_$i$SH) $(cat "$O/it_$X.txt")"
  else RC=2
    RES3="NOT CLEAN after $i (last route ${N}_$i$SH; next sizes sizes_$((i + 1)).vh) $(cat "$O/it_$X.txt")"
  fi
fi
# Flow v7 (2026-11-19): the search phase is ON by default (AUTO_SEARCH=0 turns it off), with graphsearch's all-sites
# candidates (AUTO_SEARCH_ARGS default "--all-sites --buildable-only --wire 1000"; "--depth-only" was xorgap's first
# form). PROGRAM General-first item 1 asks for exactly this: "where the latches go and how deep the links are (the event
# graph's search, run inside the flow)". It can only ship a route that is rule-CLEAN and measured faster than the
# loop's own; otherwise the loop's route ships unchanged. Farm nsearch1 (no-list flow, 18 finished loops): countloop
# 26.60 -> 20.92, 22.15 -> 21.37, 25.80 -> 20.45 ns (s4 unchanged); xorshift / collatz unchanged (their cycles sit at
# the rising-only floor, which storage cannot move); every draw passing.
[ "${AUTO_SEARCH:-1}" = 1 ] && search_phase
echo "$RES3" | tee -a "$O/result.txt"
exit "$RC"
