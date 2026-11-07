#!/usr/bin/env bash
# Probe E9ArbNet negative controls on seed d slow. Each must turn VERDICT into ARB-LINK FAILS, for the
# reason given (outputs results/xan_d_slow_<TAG>.txt).
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
S=${S:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad}
i=$S/e8mux/w/d/new; C=$S/E9Par/out/d/cert_slow.json; O=$S/E9ArbNet/out/d
export OL=${OL:-$S/E9ArbNet/ov} PYTHONHASHSEED=0 XA_ARB=fix
for t in swap drop ip noorder; do
  python3 "$HERE/gen.py" $i/skel.json $i/skel_slow.bands.json $C $O/arb_slow_NEG$t.json --neg-$t > /dev/null
  "$HERE/xan.sh" $i/skel.json $i/skel_slow.bands.json $C $O/arb_slow_NEG$t.json 2>&1 | grep -v '^\[slot\]' > "$HERE/results/xan_d_slow_NEG$t.txt"
done
# NEGband: ugrant$LUT5/I2 (merge11's g1 q read) +1 ps; the arbiter data is regenerated on the mutated bands
python3 "$HERE/mutband.py" $i/skel_slow.bands.json $O/slow_NEGband.bands.json 'urig.udut.ucontrol_merge11.uarb1.ugrant$LUT5/I2' 1
python3 "$HERE/gen.py" $i/skel.json $O/slow_NEGband.bands.json $C $O/arb_slow_NEGband.json > /dev/null
"$HERE/xan.sh" $i/skel.json $O/slow_NEGband.bands.json $C $O/arb_slow_NEGband.json 2>&1 | grep -v '^\[slot\]' > "$HERE/results/xan_d_slow_NEGband.txt"
for t in swap drop ip noorder band; do
  f="$HERE/results/xan_d_slow_NEG$t.txt"
  echo "NEG$t: $(grep -h 'ArbOK [0-9]' $f | cut -c11-) | $(grep -h '  FAIL' $f | sort | uniq -c | tr -s ' ' | tr '\n' ';') | $(tail -1 $f | cut -c1-30)"
done
