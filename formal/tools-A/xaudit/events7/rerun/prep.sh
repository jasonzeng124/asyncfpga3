#!/usr/bin/env bash
# E7r: regenerate the inputs of run7.sh exactly as events6/run6.sh made them (net.json, bands,
# skel.py skeleton + skeleton bands) into $I (default /tmp/events6/out), with net.json md5s printed
# against events5/builds.txt. No Lean here.
set -u
HERE="$(cd "$(dirname "$0")/.." && pwd)"
I=${I:-/tmp/events6/out}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
IN="$HERE/../events5/inputs"; G="$HERE/../gcd/inputs"
for s in ${SEEDS:-d 3 4 5}; do
  mkdir -p $I/$s
  [ -e $I/$s/net.json ] || { [ $s = d ] && xz -dc $G/net_d.json.xz > $I/$s/net.json || xz -dc $IN/net_$s.json.xz > $I/$s/net.json; }
  echo "$s net.json md5 $(md5sum < $I/$s/net.json | cut -c1-32)"
  for c in ${CORNERS:-slow fast indep gb}; do
    if [ ! -e $I/$s/$c.bands.json ]; then
      if [ $s = d ] && [ $c != gb ]; then xz -dc $G/bands_d_$c.json.xz > $I/$s/$c.bands.json
      else xz -dc $IN/bands_${s}_$c.json.xz > $I/$s/$c.bands.json; fi
    fi
    python3 "$HERE/../events4/skel.py" $I/$s/net.json $I/$s/$c.bands.json $I/$s/skel.json $I/$s/skel_$c.bands.json > /dev/null
    echo "$s $c skel $(md5sum < $I/$s/skel.json | cut -c1-12) bands $(md5sum < $I/$s/skel_$c.bands.json | cut -c1-12)"
  done
done
