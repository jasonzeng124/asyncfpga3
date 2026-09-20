#!/usr/bin/env bash
# Build an SDF back-annotated gate-level simulation of a ROUTED design.
#
#     cells/gls/build.sh [design]        # default gcd_hw
#
# Sources live here and in git; everything generated lands in cells/build/gls/<design>/
# and is gitignored, because it is ~900 MB per design and all of it is a
# function of two files:
#
#     cells/build/hw/<design>/<design>_routed.json     nextpnr's routed design
#     cells/build/hw/<design>/<design>.sdf             nextpnr's routed SDF
#
# WHY A COPY AND A STAMP.  A netlist from one place-and-route annotated with the
# SDF of another is not a weaker simulation, it is a meaningless one -- the
# instance names still match, so nothing complains, and every number it prints
# is invented.  build_hw.sh rewrites both files on every run, so this script
# takes its own copy up front, records the md5 of each, and refuses to proceed
# if the pair it was handed did not come out of the same build.  The stamp is
# echoed by every run, so a result can always be traced to the route it belongs
# to.  See also verify/tighten.py, which prints "toolchain UNSTAMPED" for the
# same reason: a routed number without its build is not a measurement.
set -euo pipefail

DESIGN=${1:-gcd_hw}
# build_hw.sh writes to a RELATIVE build/hw/$TOP and is run from cells/, so the
# routed output lives under cells/build/, not the repo-root build/.  Both exist
# and hold different things; picking the wrong one silently finds nothing.
CELLS=$(cd "$(dirname "$0")/.." && pwd)
SRC=$CELLS/gls
HW=$CELLS/build/hw/$DESIGN
WORK=$CELLS/build/gls/$DESIGN

J=$HW/${DESIGN}_routed.json
S=$HW/${DESIGN}.sdf

for f in "$J" "$S"; do
    [ -f "$f" ] || { echo "missing $f -- run cells/hw/build_hw.sh $DESIGN first" >&2
                     exit 1; }
done

# Same build?  nextpnr writes the JSON and the SDF back to back at the end of
# one run, so a gap of more than a couple of minutes means they are from two.
dj=$(stat -c %Y "$J"); ds=$(stat -c %Y "$S")
gap=$(( dj > ds ? dj - ds : ds - dj ))
if [ "$gap" -gt 120 ]; then
    echo "REFUSING: $(basename "$J") and $(basename "$S") were written ${gap}s apart." >&2
    echo "They are probably from different builds, and annotating one route's" >&2
    echo "netlist with another route's delays produces silent nonsense." >&2
    echo "Re-run cells/hw/build_hw.sh $DESIGN so both come from one place-and-route." >&2
    exit 1
fi

mkdir -p "$WORK"
cp "$J" "$WORK/routed.json"
cp "$S" "$WORK/routed.sdf"

{   echo "design:    $DESIGN"
    echo "built:     $(date -d @"$dj" '+%Y-%m-%d %H:%M:%S')"
    echo "stamped:   $(date '+%Y-%m-%d %H:%M:%S')"
    echo "routed.json md5 $(md5sum < "$WORK/routed.json" | cut -d' ' -f1)  <- $J"
    echo "routed.sdf  md5 $(md5sum < "$WORK/routed.sdf"  | cut -d' ' -f1)  <- $S"
    if [ -f "$HW/toolchain.txt" ]; then
        cat "$HW/toolchain.txt"
    else
        echo "toolchain: UNSTAMPED -- which nextpnr produced this route is not recorded"
    fi
} > "$WORK/provenance.txt"

echo "== provenance =="
cat "$WORK/provenance.txt"
echo

export GLS_WORK=$WORK
cd "$WORK"

echo "== generating netlist =="
python3 "$SRC/gen.py"
python3 "$SRC/gen_probe.py" urig.   # last-transition probe, for locating a wedge
python3 "$SRC/gen_chan.py"          # per-channel activity: wedge vs spin
# The testbenches watch signals by their RTL name; gen.py's wire numbers
# belong to one route, so they are resolved here rather than pasted in.
python3 "$SRC/gen_signals.py"

echo "== compiling =="
# gate.vvp routes every delay through iverilog's SDF annotator, which NAMES each
# entry it cannot place -- so silence from it is the proof that all of them
# landed, and that is the acceptance gate.  It costs ~6 min of annotator time
# before time 0 (the annotator rescans the scope tree per entry).
iverilog -gspecify -I. -o gate.vvp "$SRC/tb_gate.v" netlist.v "$SRC/prims.v"
# run_baked.vvp is the same numbers from the same parse, baked in as parameters,
# so it starts in seconds.  Equivalence is not assumed: a full run of each was
# diffed and every event timestamp is identical.
iverilog -gspecify -DGLS_TRANSPORT_IC -I. -o run_baked.vvp "$SRC/tb_run.v" netlist_baked.v "$SRC/prims.v" 2>&1 \
    | grep -v 'procedural continuous' || true

cat <<EOF

built in $WORK

  gate:        vvp gate.vvp
               must print ANNOTATE_DONE and NO 'SDF WARNING'/'SDF ERROR' lines.
               An unannotated run looks like it works and means nothing --
               iverilog 11 accepts (INTERCONNECT ...) and applies none of it,
               which is why gen.py rewrites every one as an IOPATH on an ICBUF.

  one vector:  vvp run_baked.vvp +VEC=6 +TEND=150000 +QUIET=200000
               TEND/QUIET in ns; VEC indexes the table in cells/hw/gcd_rig.v.

  all 16:      cells/gls/run.sh $DESIGN
EOF
