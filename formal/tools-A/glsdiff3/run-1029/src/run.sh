#!/usr/bin/env bash
# Sweep every vector in the rig's table through the back-annotated simulation.
#
#     cells/gls/run.sh [design] [-j N]
#
# Env: TEND (ns, default 150000)   how long to simulate
#      QUIET (ns, default 200000)  give up if nothing completes by then
#
# ~30 s per vector at TEND=150000, and they are independent, so this runs them
# in parallel.  Default -j is 4: each process holds the whole 14k-cell design,
# so this is bounded by memory, not by cores.
set -euo pipefail

DESIGN=${1:-gcd_hw}
[ "${1:-}" = "-j" ] && DESIGN=gcd_hw
CELLS=$(cd "$(dirname "$0")/.." && pwd)
WORK=$CELLS/build/gls/$DESIGN

PAR=4
while [ $# -gt 0 ]; do
    [ "$1" = "-j" ] && { PAR=$2; shift 2; continue; }
    shift
done

TEND=${TEND:-150000}
QUIET=${QUIET:-200000}

[ -x "$WORK/run_baked.vvp" ] || {
    echo "no simulation in $WORK -- run cells/gls/build.sh $DESIGN first" >&2
    exit 1; }

cd "$WORK"
mkdir -p sweep
echo "== provenance =="; cat provenance.txt; echo
echo "TEND=${TEND} ns  QUIET=${QUIET} ns  -j${PAR}"
echo

for v in $(seq 0 15); do
    while [ "$(jobs -rp | wc -l)" -ge "$PAR" ]; do sleep 2; done
    ( /usr/bin/time -f "WALL %e s" vvp run_baked.vvp \
        "+VEC=$v" "+TEND=$TEND" "+QUIET=$QUIET" > "sweep/v$v.log" 2>&1 ) &
done
wait

echo "== result =="
for v in $(seq 0 15); do
    printf "  vector %2d  %s\n" "$v" \
        "$(grep -m1 -E 'RESULT|LAPS|TIMEOUT|livelock|wedge' "sweep/v$v.log" \
           || echo 'no verdict line -- see sweep/v'"$v"'.log')"
done
cat <<'EOF'

Read a FAIL here against the board before believing it.  This simulation is
more pessimistic than silicon by construction: nextpnr's cell arcs are a flat
124 ps on O6 where the part's own are 56-152 ps and pin- and edge-dependent
(verify/tighten.py's header calls these "the weaker half of every number").
An earlier route failed 11 of 16 here where the board failed 7, so four of
those were its own pessimism rather than the design's.

On the route stamped 392abe70/aae1011d it fails EXACTLY the board's seven --
5, 6, 7, 8, 11, 12, 13 -- which is why this is now the place to debug them.
Two cautions on that match.  It is a match of PASS/FAIL MASKS; nothing on
disk ties the programmed bitstream to that md5 pair, so it is not proof the
two ran the same build.  And a failing vector reports laps=0: not one gcd
ever completes, so "how many laps" cannot rank the failures by severity.

A TIMEOUT here is only meaningful against the design's own timescale.  A
passing gcd takes ~3.2 us, and rig_rst is re-released at the window edge near
979 us, so TEND=150000 already gives a failing vector ~300 passing-gcd
latencies to produce one lap.  Raising TEND past the window edge buys less
than it looks like it does -- the ring restarts there.
EOF
