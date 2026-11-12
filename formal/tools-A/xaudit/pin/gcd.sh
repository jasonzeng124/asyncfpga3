#!/usr/bin/env bash
# gcd_hw R5 part of formal/notes/A-events2pin.md: per-pin (BackPin) margins from A-events4's
# counter-domain analysis, per seed and corner.  UNTRUSTED (gcd's control is outside xevents2's
# recognised domain; see gcdpin.py).
#   seeds: d 3 4 5 (gcd_hw R5 builds, nextpnr sha256 9c732bc6303458df; routed JSONs reproduced
#   md5-identical to gcd/inputs/builds.txt by the events5 probe in /tmp/events5/out/<seed>/;
#   prjxray arcs from xray_delay.py md5 99b10a6d in /tmp/gcdx/<seed>/arcs.tsv).
# Seed d uses the committed inputs (gcd/inputs) exactly as events4/run.sh does.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
X=$HERE/..; E4=$X/events4
W=/tmp/events2pin/gcd; mkdir -p $W
R=$HERE/results; mkdir -p $R
ROUTED=${ROUTED:-/tmp/events5/out}
ARCS=${ARCS:-/tmp/gcdx}
for S in ${SEEDS:-d 3 4 5}; do
  for c in slow fast indep; do
    if [ $S = d ]; then
      [ -e $W/net_d.json ] || xz -dc $X/gcd/inputs/net_d.json.xz > $W/net_d.json
      [ -e $W/bands_d_$c.json ] || xz -dc $X/gcd/inputs/bands_d_$c.json.xz > $W/bands_d_$c.json
    else
      [ -e $W/bands_${S}_$c.json ] || python3 -I $X/routed2x.py $ROUTED/$S/gcd_hw_routed.json \
          --xray-arcs $ARCS/$S/arcs.tsv --corner $c --out $W/net_$S.json --bands $W/bands_${S}_$c.json \
          > $W/routed2x_${S}_$c.txt
    fi
    python3 "$E4/skel.py" $W/net_$S.json $W/bands_${S}_$c.json $W/skel_$S.json $W/skel_bands_${S}_$c.json
    python3 "$E4/ana.py" $W/skel_$S.json $W/skel_bands_${S}_$c.json --label "$S $c" --json $W/sk_${S}_$c.json \
        > $W/ana_${S}_$c.txt || true
    python3 -I "$HERE/gcdpin.py" $W/sk_${S}_$c.json $W/bands_${S}_$c.json --label "seed $S $c"
  done
done | tee $R/gcd_summary.txt
