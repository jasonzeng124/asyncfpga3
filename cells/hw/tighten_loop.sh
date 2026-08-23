#!/usr/bin/env bash
# Size every matched delay in a compiled kernel from ITS OWN ROUTE, then build
# again with those sizes and check they still hold.
#
#   hw/tighten_loop.sh xorshift [iterations]
#   BDC_CONST_FOLD=1 hw/tighten_loop.sh xorshift
#
# WHY THIS DID NOT EXIST.  verify/tighten.py has always measured what each
# delay line should be for the route in front of it, and verify/resize.sh has
# always driven that to a fixed point -- but only for soak_top, a hand-written
# design whose delays are `define BD_SZ_* macros.  A COMPILED kernel's chains
# were sized by bdc/emit.py's unmeasured estimate and stayed there, because
# hw/gen_bench.py instantiated the kernel with none of its DELAY_<INST>
# parameters overridden.  tighten.py's proposals had nothing to attach to.
#
# What that cost, measured on xorshift: chains built to 122.2 ns where the
# route needs 76.0.  With region fusion on, 122.7 ns where the route needs
# 30.2 -- fusion cut the requirement by 2.5x and moved the board by 3%,
# because nothing shortened the line it had just made shortenable.
#
# THE ALTERNATION MATTERS, AND HERE IS THE MEASUREMENT THAT PROVES IT.  Sizes
# belong to one route, and a route built from sizes is not the route they were
# measured on.  The first version of this loop assumed the only thing that
# moved was the datapath.  It is not:
#
#   uaddi0, unsized route:  24 links = 10044 ps  ->  418 ps per element
#   uaddi0, sized route:     8 links =  2432 ps  ->  304 ps per element
#
# THE DELAY ELEMENT ITSELF GOT 27% CHEAPER.  A 24-element chain has to be
# spread across the die and pays inter-tile hops; the 8-element chain that
# replaced it is local and does not.  So a proposal computed as "N elements at
# the current cost" under-delivers the moment it is applied, and it
# under-delivers in the DANGEROUS direction -- short.  On xorshift that turned
# a clean rule A into 8 violations in one step, chain 122.7 ns -> 15.8 ns with
# uaddi0 landing 981 ps under its own datapath.
#
# That is not a reason to distrust the sizing; it is the reason the loop has to
# alternate rather than compute once.  Each iteration measures from the CURRENT
# route and rebuilds, and tighten.py's proposal on a VIOLATING route is already
# the corrected, longer one (verify/tighten.py:1020 -- want = n + ceil(-margin
# / per)), so a failed iteration carries its own fix into the next.  Same
# argument verify/resize.sh's header makes; this is that loop pointed at a
# compiled kernel.
#
# AND IT ONLY EVER SHORTENS UNDER A GATE.  Shortening a matched delay is the
# dangerous direction -- too short is not a simulation failure, it is silent
# corruption at a PVT corner no sim here models.  So every iteration re-runs
# the rule against the route the new sizes produced; an iteration that fails it
# is never a candidate, and the loop keeps the SHORTEST build that passed.
#
# The last build is not automatically the answer.  Sizes and route are a pair,
# so restoring a winning sizes file means routing again, and that route can
# differ from the one the sizes were validated on.  This script therefore
# re-checks after the restore, and if the restored build does not pass on its
# own route it ships NO sizes at all -- bdc/emit.py's generous estimate --
# rather than a bitstream whose margins were never confirmed.
#
# IT OSCILLATES WITHOUT A RATCHET, SO THE PROPOSALS ONLY EVER GO UP.
# Measured on xorshift, taking each route's proposal at face value:
#
#   uaddi0:  8 -> 12 ->  7 ->  8       chain 122.7 -> 15.8 -> 21.8 -> 16.0 ns
#   ucmpi0: 12 -> 17 -> 15 -> 14       rule A viol.    8      5      6
#   umux0:   0 ->  1 ->  0 ->  1
#
# A clean period-2 cycle: build what the route asked for, and the route you
# get asks for something else.  Nothing ever passed.  verify/converge.sh hit
# the identical wall on rule E and its own message is the right diagnosis --
# "the padding is changing the route as fast as it is fixing it... no
# per-channel constant taken from build N is still valid on build N+1" -- and
# it refuses to continue rather than chase it.
#
# Rule A differs from rule E in the one way that matters here: its knob has a
# MONOTONE SAFE DIRECTION.  A longer matched delay is never incorrect, only
# slower, whereas rule E's padding can be applied to the wrong link and make
# the violation worse.  So this loop keeps a per-cell RUNNING MAXIMUM of every
# length any route has asked for and never proposes below it.  Sizes are then
# non-decreasing, the sequence is bounded by the unsized estimate, and it
# terminates.
#
# Be honest about what that buys: the result is NOT "the tightest safe size".
# It is "the largest requirement seen across the routes actually visited",
# which is a bound, not an optimum -- and a route never visited could ask for
# more.  That is why the gate still runs on the final build and still refuses
# to ship anything it did not confirm.
#
# THE GATE IS RULE A, NOT tighten.py's EXIT CODE.  This is the one thing here
# that is easy to get wrong, and the first version of this script got it
# wrong.  tighten.py exits nonzero if ANY rule reports a violation, and on
# every kernel built so far the nonzero comes from rule D -- the select
# screen -- which fires on all 8 bd_steer cells at iteration 0, before this
# script has changed anything.  tighten.py's own source says why: rule D pairs
# the EARLIEST possible request against the LATEST select with every input
# assumed to launch at t=0, so it cannot see matched delay already upstream,
# and acting on its number was measured to change nothing (same netlist,
# SELECT_PAD 4 vs 32, byte-identical failing mask on silicon).  Gating on the
# exit code means reverting every build forever while reporting that the
# sizes were unsafe.  Rule A -- "the request is the last thing its cell
# emits" -- is the rule that actually catches a delay line shortened past its
# own datapath, so rule A is what gates.  Rule D is still printed and still
# counted; it is a standing placement issue, not this loop's verdict.
set -eu
cd "$(dirname "$0")/.."

K=${1:-xorshift}
MAXIT=${2:-3}
TOP=${K}_bench_gen
SIZES=build/gen/${TOP}_sizes.vh
SDF=build/hw/${TOP}/${TOP}.sdf
HIST=build/tighten_loop/$K
mkdir -p "$HIST"

# Rule A's section of a tighten.py log, and whether anything in it failed.
# Sections are "<LETTER>. <text>" at column 0, so rule A runs from its header
# to rule B's.
rule_a_violations() {
    awk '/^A\. /{a=1;next} /^B\. /{a=0} a' "$1" | grep -c "VIOLATION" || true
}

# ns of matched delay actually built, and ns the route needs, from rule A.
totals() {
    awk '/^A\. /{a=1;next} /^B\. /{a=0} a' "$1" | python3 -c '
import re, sys
r = re.findall(r"^\s+\S+\s+(\d+) links\s+(\d+) ps\s+req\s+(\d+)\s+peak\s+(\d+)"
               r"\s+guard\s+(\d+)", sys.stdin.read(), re.M)
print(f"{sum(int(x[1]) for x in r)/1000:.1f} "
      f"{sum(int(x[3])+int(x[4]) for x in r)/1000:.1f} {len(r)}" if r else "0 0 0")'
}

report() {   # $1 = tighten log, $2 = label
    read -r built need n <<<"$(totals "$1")"
    v=$(rule_a_violations "$1")
    d=$(awk '/^D\. /{d=1;next} /^E\. |^$/{ } d' "$1" | grep -c "VIOLATION" || true)
    echo "   $2: $n delay-bearing cell(s), chain built ${built} ns, route needs ${need} ns"
    echo "        rule A violations: $v   (rule D screen, informational: $d)"
    RULE_A=$v
}

echo "== iteration 0: build with no measured sizes =="
rm -f "$SIZES" "$HIST/ratchet.vh"
BD_SIZES=none BD_SIZES_GATE=0 ./hw/build_bench.sh "$K" > "$HIST/build.0.log" 2>&1 || {
    echo "BUILD FAILED"; tail -20 "$HIST/build.0.log"; exit 1; }
python3 verify/tighten.py "$SDF" > "$HIST/tighten.0.log" 2>&1 || true
report "$HIST/tighten.0.log" "unsized"
read -r BASE_NS _ _ <<<"$(totals "$HIST/tighten.0.log")"
[ "$RULE_A" -eq 0 ] || echo "   WARNING: rule A already fails before any sizing"

BEST=""          # shortest sizes file that passed rule A on its own route
BEST_NS=""
LAST=""

for i in $(seq 1 "$MAXIT"); do
    echo "== iteration $i: size from that route, rebuild, re-check =="
    python3 verify/tighten.py "$SDF" --emit "$SIZES" > "$HIST/emit.$i.log" 2>&1 || true
    [ -e "$SIZES" ] || { echo "   tighten.py wrote no sizes -- stopping"; break; }
    cp "$SIZES" "$HIST/raw.$i.vh"
    RATCHET=$HIST/ratchet.vh
    python3 - "$HIST/raw.$i.vh" "$RATCHET" "$SIZES" <<'RPY'
import pathlib, re, sys
raw, acc, out = (pathlib.Path(a) for a in sys.argv[1:4])
def read(p):
    return {m[1]: int(m[2]) for m in
            re.finditer(r"^`define (\S+) (\d+)", p.read_text(), re.M)} \
           if p.exists() else {}
new, prev = read(raw), read(acc)
merged = dict(prev)
raised = []
for k, v in new.items():
    if v > merged.get(k, -1):
        if k in prev:
            raised.append(f"{k.split('_UDUT_')[-1]} {prev[k]}->{v}")
        merged[k] = v
hdr = ["// GENERATED by hw/tighten_loop.sh from verify/tighten.py proposals.",
       "// Per-cell RUNNING MAXIMUM over every route this loop has visited --",
       "// NOT any single route's answer.  A matched delay is only ever unsafe",
       "// when too SHORT, so taking the max across routes is the safe merge",
       "// and it is what makes this loop terminate instead of oscillate.",
       ""]
out.write_text("\n".join(hdr + [f"`define {k} {merged[k]}" for k in sorted(merged)]) + "\n")
acc.write_text(out.read_text())
print("   ratchet: " + (", ".join(raised) if raised else "nothing raised")
      + f"  ({len(merged)} cell(s))")
RPY
    cp "$SIZES" "$HIST/sizes.$i.vh"

    # A proposal identical to the one already built is a fixed point, and the
    # route it produced has already been judged.  Stop before paying for it.
    if [ -n "$LAST" ] && cmp -s "$HIST/sizes.$i.vh" "$LAST"; then
        echo "   CONVERGED: the proposal stopped moving"
        break
    fi
    LAST="$HIST/sizes.$i.vh"

    if ! BD_SIZES_GATE=0 ./hw/build_bench.sh "$K" > "$HIST/build.$i.log" 2>&1; then
        echo "   BUILD FAILED with these sizes -- not a candidate"
        tail -4 "$HIST/build.$i.log" | sed 's/^/     /'
        break
    fi

    python3 verify/tighten.py "$SDF" > "$HIST/tighten.$i.log" 2>&1 || true
    report "$HIST/tighten.$i.log" "sized (pass $i)"

    if [ "$RULE_A" -ne 0 ]; then
        # NOT a failure of the loop -- this is the feedback the loop runs on.
        # The delay element's own cost moved when the chain got shorter, so
        # these lengths under-deliver.  tighten.py has already priced the fix
        # off THIS route; the next iteration builds it.
        echo "   rejected: $RULE_A cell(s) whose request no longer trails their"
        echo "   own datapath.  Re-sizing from this route (proposals go UP)."
        awk '/^A\. /{a=1;next} /^B\. /{a=0} a' "$HIST/tighten.$i.log" \
            | grep "VIOLATION" | head -3 | sed 's/^/     /'
        continue
    fi

    read -r built need n <<<"$(totals "$HIST/tighten.$i.log")"
    if [ -z "$BEST_NS" ] || awk "BEGIN{exit !($built < $BEST_NS)}"; then
        BEST="$HIST/sizes.$i.vh"; BEST_NS="$built"
        echo "   ACCEPTED as best so far: ${built} ns of matched delay"
    else
        echo "   passes, but ${built} ns is not shorter than the best ${BEST_NS} ns"
    fi
done

echo
if [ -z "$BEST" ]; then
    echo "RESULT: no sized build passed rule A on its own route."
    echo "Shipping bdc/emit.py's estimate -- unmeasured, generous, and safe."
    rm -f "$SIZES"
    BD_SIZES_GATE=0 ./hw/build_bench.sh "$K" > "$HIST/build.final.log" 2>&1 || true
else
    echo "RESULT: best passing build carries ${BEST_NS} ns of matched delay"
    echo "        (unsized baseline was ${BASE_NS} ns)"
    if ! cmp -s "$BEST" "$SIZES"; then
        echo "        restoring it and routing again..."
        cp "$BEST" "$SIZES"
        BD_SIZES_GATE=0 ./hw/build_bench.sh "$K" > "$HIST/build.final.log" 2>&1 || true
        python3 verify/tighten.py "$SDF" > "$HIST/tighten.final.log" 2>&1 || true
        report "$HIST/tighten.final.log" "restored"
        if [ "$RULE_A" -ne 0 ]; then
            echo "   The restored build does NOT pass on the route it just got."
            echo "   Sizes and route are a pair and this pairing was never"
            echo "   validated, so it is not shippable.  Falling back to the"
            echo "   unmeasured estimate."
            rm -f "$SIZES"
            BD_SIZES_GATE=0 ./hw/build_bench.sh "$K" > "$HIST/build.fallback.log" 2>&1 || true
        fi
    fi
fi

echo
if [ -e "$SIZES" ]; then
    echo "final: $(grep -c '^`define' "$SIZES") measured size(s) in $SIZES"
else
    echo "final: no sizes applied -- kernel is at bdc/emit.py's estimate"
fi
echo "bitstream build/hw/$TOP/$TOP.bit"
