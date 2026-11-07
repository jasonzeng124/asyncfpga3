#!/usr/bin/env bash
# A-events6: gcd_hw seeds d 3 4 5 x corners slow fast indep(mixed) gb:
#   skel.py (events4) -> cert6.py (untrusted certificate) -> xevents5 (Lean checker, lean --run on a
#   private olean overlay until the lakefile stanza exists) ; plus ana5.py --lutpin for comparison.
# Inputs as events5/run5.sh. Outputs: events6/xe5_<seed>_<corner>.txt, ana5lp_<seed>_<corner>.txt
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
O=${O:-/tmp/events6/out}
XE5=${XE5:-$HERE/xe5.sh}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
IN="$HERE/../events5/inputs"; G="$HERE/../gcd/inputs"
for s in ${SEEDS:-d 3 4 5}; do
  mkdir -p $O/$s
  [ -e $O/$s/net.json ] || { [ $s = d ] && xz -dc $G/net_d.json.xz > $O/$s/net.json || xz -dc $IN/net_$s.json.xz > $O/$s/net.json; }
  for c in ${CORNERS:-slow fast indep gb}; do
    if [ ! -e $O/$s/$c.bands.json ]; then
      if [ $s = d ] && [ $c != gb ]; then xz -dc $G/bands_d_$c.json.xz > $O/$s/$c.bands.json
      else xz -dc $IN/bands_${s}_$c.json.xz > $O/$s/$c.bands.json; fi
    fi
    python3 "$HERE/../events4/skel.py" $O/$s/net.json $O/$s/$c.bands.json $O/$s/skel.json $O/$s/skel_$c.bands.json > /dev/null
    python3 "$HERE/cert6.py" $O/$s/skel.json $O/$s/skel_$c.bands.json $O/$s/cert_$c.json > $O/$s/cert_$c.txt 2>&1
    $XE5 $O/$s/skel.json $O/$s/skel_$c.bands.json $O/$s/cert_$c.json > "$HERE/xe5_${s}_$c.txt" 2>&1
    python3 "$HERE/../events5/ana5.py" $O/$s/skel.json $O/$s/skel_$c.bands.json --lutpin --label ${s}_${c}_lutpin > "$HERE/ana5lp_${s}_$c.txt" 2>&1
    echo "$s $c: $(tail -1 $HERE/xe5_${s}_$c.txt | cut -c1-60)"
  done
done
