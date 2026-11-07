#!/usr/bin/env bash
# E7r: rerun the rebuilt xevents7 (lean --run on /tmp/events7/olean, built by ../mk.sh) on the
# 16 rows, the ablation and the negative controls, writing outputs HERE (events7/rerun/) and
# comparing each with the committed ../xe7_*.txt ([slot] lines stripped).
# Inputs: prep.sh ($I), certificates from ../cert7.py ($O, made here if missing).
set -u
R="$(cd "$(dirname "$0")" && pwd)"; E="$R/.."
I=${I:-/tmp/events6/out}; O=${O:-/tmp/events7/out}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
J=${JOBS:-3}
one() {  # skel bands cert out
  "$E/xe7.sh" "$1" "$2" "$3" 2>&1 | grep -v '^\[slot\]' > "$4"
}
rows=()
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast indep gb}; do rows+=("$s $c"); done; done
for r in "${rows[@]}"; do
  set -- $r; s=$1; c=$2
  [ -e $O/$s/cert_$c.json ] || python3 "$E/cert7.py" $I/$s/skel.json $I/$s/skel_$c.bands.json $O/$s/cert_$c.json > "$R/cert7_${s}_$c.txt" 2>&1
  one $I/$s/skel.json $I/$s/skel_$c.bands.json $O/$s/cert_$c.json "$R/xe7_${s}_$c.txt" &
  while [ "$(jobs -rp | wc -l)" -ge $J ]; do sleep 1; done
done
wait
for r in "${rows[@]}"; do
  set -- $r; s=$1; c=$2
  if cmp -s "$R/xe7_${s}_$c.txt" "$E/xe7_${s}_$c.txt"; then st=IDENTICAL; else st=DIFFERS; fi
  echo "$s $c: $st | $(tail -1 "$R/xe7_${s}_$c.txt" | cut -c1-40)"
done
