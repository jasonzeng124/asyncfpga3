#!/usr/bin/env bash
# Run the pure-link ring rig on the board and report ns per handshake stage.
#
#   hw/run_ro_link.sh [label]
#
# Its only job beyond calling xsdb is to hand the tcl the counter-closure
# gate: nextpnr's post-route Fmax for each ring's counter clock, scraped out
# of the build that produced this bitstream.  Without those numbers the tcl
# reports every point UNGATED, and an undercount at the short end would bend
# the fit in exactly the direction that makes the protocol look cheap -- see
# hw/ro_link_ps.v's header.
set -eu
cd "$(dirname "$0")/.."

TOP=ro_link_ps
OUT=build/hw/$TOP
BIT=$OUT/$TOP.bit
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
LABEL=${1:-$TOP}

[ -e "$BIT" ] || { echo "no bitstream: $BIT  (hw/build_hw.sh $TOP)"; exit 2; }

# nextpnr prints the frequency table twice -- once pre-route, once post.  The
# post-route pass is the one that describes the bitstream, so take the LAST
# occurrence of each ring.  Ordered ring 0 first, which is what the tcl
# expects, because the log emits them highest-index first.
FMAX=$(for i in 0 1 2 3 4; do
    grep -oP "(?<=Max frequency for clock 'bridge_i.ring\[$i\].ck': )[0-9.]+" \
        "$OUT/pnr.log" | tail -1
done | paste -sd,)

echo "counter-closure gate (post-route Fmax, MHz, ring 0 first): $FMAX"
BD_RO_FMAX="$FMAX" "$XSDB" hw/xsdb_ro_link.tcl "$BIT" "$LABEL"
