#!/usr/bin/env bash
# Probe HDsub: rerun xevents8 (Events8Main, lean --run on the overlay $OL) on the same inputs as run9.sh,
# into $O8 (not into events8/), and diff each output against the committed events8/xe8_<seed>_<corner>.txt.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
I=${I:-/tmp/events6/out}; O8=${O8:-/tmp/events9/cmp8}; OL=${OL:-/tmp/events9/olean}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 PATH=$HOME/.elan/bin:$PATH
J=${JOBS:-2}
x8() { cd /home/user/asyncfpga3/formal/lean && FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="'$OL':$LEAN_PATH" exec lean -DautoImplicit=false --run Formal/Core/XAudit/Events8Main.lean "$@"' sh "$@"; }
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast indep gb}; do
  mkdir -p $O8/$s
  python3 "$HERE/../events8/cert8.py" $I/$s/skel.json $I/$s/skel_$c.bands.json $O8/$s/cert_$c.json > $O8/cert8_${s}_$c.txt 2>&1
  ( x8 $I/$s/skel.json $I/$s/skel_$c.bands.json $O8/$s/cert_$c.json 2>&1 | grep -v '^\[slot\]' > $O8/xe8_${s}_$c.txt ) &
  while [ "$(jobs -rp | wc -l)" -ge $J ]; do sleep 1; done
done; done
wait
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast indep gb}; do
  if cmp -s $O8/xe8_${s}_$c.txt "$HERE/../events8/xe8_${s}_$c.txt"; then r="identical to committed"; else r="DIFFERS from committed"; fi
  echo "$s $c: $(tail -1 $O8/xe8_${s}_$c.txt | cut -c1-60) | $r"
done; done
