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
On 2026-08-17 it failed 11 of 16 vectors where the board failed 7, so four of
its failures were its own pessimism, not the design's.
EOF
