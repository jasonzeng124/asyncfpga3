#!/usr/bin/env bash
# A-kapres: restore the committed inputs, then sweep xevents5 over corner cells for every seed and kappa.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
O=/tmp/kapres/in; X="$HERE/.."
for s in d 3 4 5; do
  mkdir -p $O/$s
  if [ $s = d ]; then
    [ -e $O/$s/net.json ] || xz -dc $X/gcd/inputs/net_d.json.xz > $O/$s/net.json
    for c in slow fast; do [ -e $O/$s/$c.bands.json ] || xz -dc $X/gcd/inputs/bands_d_$c.json.xz > $O/$s/$c.bands.json; done
  else
    [ -e $O/$s/net.json ] || xz -dc $X/events5/inputs/net_$s.json.xz > $O/$s/net.json
    for c in slow fast; do [ -e $O/$s/$c.bands.json ] || xz -dc $X/events5/inputs/bands_${s}_$c.json.xz > $O/$s/$c.bands.json; done
  fi
done
# seeds in parallel (slot.sh bounds the Lean processes); kappas descending inside kapres.py
for s in ${SEEDS:-d 3 4 5}; do
  python3 "$HERE/kapres.py" $s --init ${INIT:-8} --depth ${DEPTH:-2} --jobs ${JOBS:-2} > /tmp/kapres/run_$s.log 2>&1 &
done
wait
cat /tmp/kapres/run_*.log
