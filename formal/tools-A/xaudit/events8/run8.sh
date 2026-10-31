#!/usr/bin/env bash
# WE4g: gcd_hw seeds d 3 4 5 x corners slow fast indep(mixed) gb, as events7/rerun/rerun.sh:
#   inputs from events7/rerun/prep.sh ($I, skel.json + skel_<corner>.bands.json per seed)
#   -> cert8.py (UNTRUSTED certificate) -> xevents8 (lean --run on /tmp/events8/olean, mk8.sh).
# At most 2 lean --run jobs at a time (parallel runs produced empty outputs before).
# Outputs here: xe8_<seed>_<corner>.txt, cert8_<seed>_<corner>.txt (cert8.py's summary)
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
I=${I:-/tmp/events6/out}; O=${O:-/tmp/events8/out}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
J=${JOBS:-2}
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast indep gb}; do
  mkdir -p $O/$s
  python3 "$HERE/cert8.py" $I/$s/skel.json $I/$s/skel_$c.bands.json $O/$s/cert_$c.json ${FLAGS:-} > "$HERE/cert8_${s}_$c${TAG:-}.txt" 2>&1
  ( "$HERE/xe8.sh" $I/$s/skel.json $I/$s/skel_$c.bands.json $O/$s/cert_$c.json 2>&1 | grep -v '^\[slot\]' > "$HERE/xe8_${s}_$c${TAG:-}.txt" ) &
  while [ "$(jobs -rp | wc -l)" -ge $J ]; do sleep 1; done
done; done
wait
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast indep gb}; do
  f="$HERE/xe8_${s}_$c${TAG:-}.txt"
  echo "$s $c: $(grep -h 'guarded pins' $f | cut -c12-140) | $(tail -1 $f | cut -c1-40)"
done; done
