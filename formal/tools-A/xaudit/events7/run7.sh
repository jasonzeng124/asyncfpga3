#!/usr/bin/env bash
# A-events7: gcd_hw seeds d 3 4 5 x corners slow fast indep(mixed) gb:
#   skeleton + bands as A-events6 (events6/run6.sh made them, in $I) -> cert7.py (untrusted
#   certificate: nodes, derivation log, items) -> xevents7 (Lean checker, lean --run on the private
#   olean overlay /tmp/events7/olean built by mk.sh until the lakefile stanza exists).
# Outputs: events7/xe7_<seed>_<corner>.txt, cert7_<seed>_<corner>.txt
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
I=${I:-/tmp/events6/out}       # skel.json, skel_<corner>.bands.json per seed (events6/run6.sh)
O=${O:-/tmp/events7/out}
XE7=${XE7:-$HERE/xe7.sh}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
for s in ${SEEDS:-d 3 4 5}; do
  mkdir -p $O/$s
  for c in ${CORNERS:-slow fast indep gb}; do
    python3 "$HERE/cert7.py" $I/$s/skel.json $I/$s/skel_$c.bands.json $O/$s/cert_$c.json ${FLAGS:-} > "$HERE/cert7_${s}_$c.txt" 2>&1
    $XE7 $I/$s/skel.json $I/$s/skel_$c.bands.json $O/$s/cert_$c.json > "$HERE/xe7_${s}_$c${TAG:-}.txt" 2>&1
    echo "$s $c: $(tail -1 $HERE/xe7_${s}_$c${TAG:-}.txt | cut -c1-70)"
  done
done
