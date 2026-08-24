#!/usr/bin/env bash
# Per-channel select padding, driven by measurement, iterated to a fixed point.
#
# WHY A LOOP AT ALL.  A bd_link's req_out is one arc from its C node and its
# data_out is two -- through the latch -- so a link driving a SELECT hands its
# consumer a request that leads its own select.  bd_link's DELAY pads req_out
# alone, which is exactly the right knob.  What nobody can know before routing
# is HOW MUCH, because the gap is dominated not by that one latch arc but by
# where the placer happened to put the link's two LUTs: measured on gcd, a
# link spends 900 ps getting from its own C node to its own latch's enable,
# while the first element of the same link's delay chain sits 150 ps away.
#
# WHY NOT A CONSTANT.  Tried, on silicon, and it does not work.  BDC_SELECT_PAD
# 4 vs 32 vs 64 -- a global multiplier on every select channel -- came out
# NON-MONOTONE: 7/16 vectors, then 16/16, then 8/16, with an unrelated one-LUT
# rig change moving the 32 case to 9/16 on its own.  24 channels x 64 elements
# is 1536 LUT1s of chain; the congestion that buys moves the skew on the
# channels that were already marginal faster than it fixes the ones it padded.
#
# WHY THIS TERMINATES.  Pads only ever grow here, and they are bounded by CAP.
# The deficit is measured per link by rule E, so a run touches the handful of
# links that measured short -- on gcd, four of them, for a total of six
# elements -- rather than all 24.  Six LUT1s in a 7000-LUT design perturb a
# route the way the global pad demonstrably did not.
#
# WHAT A FAILURE LOOKS LIKE, and it is a real outcome, not an error: a link
# that is still short at CAP, or a design where the set of short links keeps
# CHANGING from iteration to iteration.  The second one means the route is too
# sensitive for any per-channel number to be stable, and that is worth knowing
# BEFORE shipping one.  Both are reported, loudly, and exit non-zero.  The
# answer then is not a bigger number: it is to make the placer keep a link's
# C node and its latch in one slice, which is a packing decision rather than a
# pinned location.
#
#   verify/converge.sh gcd_ps [max-iterations]
set -u
cd "$(dirname "$0")/.."

DESIGN=${1:-gcd_ps}
MAX=${2:-6}
CAP=${CONVERGE_CAP:-64}

# The builder this loop iterates.  Default is hw/build_hw.sh DESIGN, exactly
# as before this was parameterised.  hw/build_bench.sh is a SIBLING build
# script (see its own header for why it must not be patched into
# build_hw.sh) that takes "<kernel> [--null]" rather than one DESIGN token,
# so its caller sets CONVERGE_BUILDER to the full command -- e.g.
#   CONVERGE_BUILDER="./hw/build_bench.sh gcd --null" verify/converge.sh gcd_null_bench_gen
# DESIGN still has to name the build's own TOP (build/hw/$DESIGN/$DESIGN.sdf
# is where this script reads the routed SDF from below), which is exactly
# what hw/build_bench.sh's own --top naming already produces
# (<kernel>_bench_gen / <kernel>_null_bench_gen) -- so DESIGN is bookkeeping
# for this script, not necessarily a literal argument to the builder.
# CONVERGE_BUILDER is intentionally split by word here, not quoted as one
# token, so it can carry a command plus its own arguments.
# shellcheck disable=SC2206
CONVERGE_BUILDER=(${CONVERGE_BUILDER:-./hw/build_hw.sh "$DESIGN"})

STATE=build/converge/$DESIGN
mkdir -p "$STATE"
PADS=$(readlink -f "$STATE")/pads.json
DELTA=$(readlink -f "$STATE")/delta.json
# pads.json is THIS INVOCATION's state, not a cache that survives to the next
# one.  It used to persist, and that quietly broke the loop it belongs to.
#
# The regression test below asks: has a link THIS LOOP ALREADY PADDED measured
# short again?  One instance is enough to declare non-convergence, because it
# means the padding is changing the route as fast as it is fixing it.  That is
# the right test for pads this invocation placed.  It is the WRONG test for
# pads inherited from an earlier invocation, whose route no longer exists --
# and this script's own abort message says so in as many words: "NO per-channel
# constant taken from build N is still valid on build N+1".  Carrying them
# forward and then treating them as evidence contradicts that.
#
# Measured on gcd, 2026-08-24: with an inherited {ulink_n85__3: 2} in the file,
# two successive repair runs aborted at iteration 1 in four minutes on state
# from a route that had already been thrown away.  Deleting the file by hand
# let the same command build and measure normally.  Worse, hw/tighten_loop.sh
# calls this script once per OUTER iteration against one state directory, so a
# persisted pads file capped the outer loop at a single sized step no matter
# what iteration budget it was given.
#
# CONVERGE_RESUME=1 keeps the file for anyone deliberately continuing a search.
# The previous file is archived either way, so nothing is silently destroyed.
if [ -f "$PADS" ] && [ "${CONVERGE_RESUME:-0}" != "1" ]; then
    cp "$PADS" "$(dirname "$PADS")/pads.prev.json"
    echo '{}' > "$PADS"
elif [ ! -f "$PADS" ]; then
    echo '{}' > "$PADS"
fi

echo "converge     $DESIGN, up to $MAX iteration(s), cap $CAP elements/link"
echo "             builder: ${CONVERGE_BUILDER[*]}"
echo "             pads $PADS${CONVERGE_RESUME:+ (RESUMED from the previous run)}"

for i in $(seq 1 "$MAX"); do
    echo
    echo "---- iteration $i: build ----"
    if ! BDC_SELECT_PADS=$PADS "${CONVERGE_BUILDER[@]}" > "$STATE/build.$i.log" 2>&1; then
        echo "  BUILD FAILED -- see $STATE/build.$i.log"
        tail -20 "$STATE/build.$i.log"
        exit 2
    fi
    SDF=build/hw/$DESIGN/$DESIGN.sdf
    echo "---- iteration $i: measure ----"
    python3 verify/skew.py "$SDF" --select-pads "$DELTA" \
        | tee "$STATE/skew.$i.log" | grep -E "select gates|guardband|element cost|VIOLATED|fix:"
    cp "$DELTA" "$STATE/delta.$i.json"

    # The non-convergence test, and getting it right matters more than it
    # looks.  The obvious test -- "the same SET of short links came back" --
    # is far too weak: measured on gcd the set was different every single
    # iteration (6 links, then 10, then 2, then 2, then 3, never repeating)
    # and the loop ran to MAX reporting nothing while plainly not settling.
    #
    # The right test is per LINK.  A link this loop has ALREADY PADDED and
    # which measures short again has had its own fix undone by the route that
    # fix produced.  That is the failure, and one instance of it is enough:
    # on gcd it happens at iteration 2, which is four builds earlier than the
    # set test noticed anything.
    n=$(python3 -c "import json,sys;print(len(json.load(open(sys.argv[1]))))" "$DELTA")
    regressed=$(python3 -c "
import json,sys
was=set(json.load(open(sys.argv[1])))
now=set(json.load(open(sys.argv[2])))
print(','.join(sorted(was & now)))" "$PADS" "$DELTA")

    if [ "$n" = "0" ]; then
        echo
        echo "  CONVERGED after $i iteration(s): every select gate clears rule E's"
        echo "  guardband on the route its own padding produced."
        python3 -c "
import json,sys
d=json.load(open(sys.argv[1]))
print('  final pads (absolute, elements):' if d else '  final pads: none needed')
for k,v in sorted(d.items()): print(f'    {k:<28} {v}')
print(f'  total added: {sum(d.values())} bd_delay element(s)')" "$PADS"
        exit 0
    fi

    if [ -n "$regressed" ]; then
        echo
        echo "  NOT CONVERGING: {$regressed} measured short again AFTER this loop"
        echo "  had already padded it.  The padding is changing the route as fast"
        echo "  as it is fixing it."
        echo
        echo "  This is not a tuning failure, it is the wrong knob.  The margins"
        echo "  in question are 76-400 ps and the build-to-build routing noise on"
        echo "  this fabric is larger than that, so NO per-channel constant taken"
        echo "  from build N is still valid on build N+1.  Do not raise the cap"
        echo "  and do not raise MAX."
        echo
        echo "  The term to remove is measured: on gcd a bd_link's C node reaches"
        echo "  its OWN latch across a median 1920 ps of routing (p90 3405, max"
        echo "  4275), while the same C node reaches its own delay chain in 639."
        echo "  Two LUTs of one cell, two nanoseconds apart, on the critical path"
        echo "  of every transfer in the design.  Fix that and the select margin"
        echo "  stops being a search."
        exit 1
    fi

    python3 - "$PADS" "$DELTA" "$CAP" <<'PYEOF'
import json, pathlib, re, sys, glob
pads, delta, cap = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), int(sys.argv[3])
cur = json.loads(pads.read_text())
add = json.loads(delta.read_text())
# A link this loop has not touched yet is already carrying whatever emit.py
# gave it, and rule E's number is ADDITIONAL to that.  Read the length it
# actually has out of the emitted parameter rather than assuming SELECT_PAD.
emitted = {}
for f in glob.glob("../build/gen/*.v"):
    for m in re.finditer(r"parameter DELAY_(ULINK_[A-Z0-9_]+) = (\d+)",
                         pathlib.Path(f).read_text()):
        emitted[m.group(1).lower()] = int(m.group(2))
over = []
for k, v in add.items():
    base = cur.get(k, emitted.get(k, 0))
    want = base + v
    if want > cap:
        over.append((k, want))
        want = cap
    cur[k] = want
pads.write_text(json.dumps(dict(sorted(cur.items())), indent=1) + "\n")
for k, w in over:
    print(f"  AT CAP: {k} wants {w} elements, capped at {cap}")
print("  next pads: " + ", ".join(f"{k}={v}" for k, v in sorted(cur.items())))
PYEOF
done

echo
echo "  STILL SHORT after $MAX iteration(s).  Rule E has not been satisfied and"
echo "  the padding has not settled.  This is a result, not a crash: report the"
echo "  remaining sites rather than raising MAX until the number goes positive."
exit 1
