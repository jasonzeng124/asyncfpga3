#!/usr/bin/env bash
# Probe E8ArbFix: events9/cert9.py (UNTRUSTED certificate, model.py's virtual arbiter core ARB=fix|old)
# + xevents9 (lean --run on the overlay $OL, events9/xe9.sh) on the E8Mux corrected bands
# (e8mux/bands.sh: $W/<seed>/new/skel.json, skel_<corner>.bands.json, each passing e8mux/checkbands.py).
#   ARB=fix (default) | old    SEEDS="d 3 4 5"  CORNERS="slow fast indep gb"  TAG=...
# Outputs: results/xe9_<seed>_<corner>_<ARB><TAG>.txt, results/cert9_<seed>_<corner>_<ARB><TAG>.txt
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"; X="$HERE/.."
S=${S:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad}
W=${W:-$S/e8mux/w}; O=${O:-$S/E8ArbFix/out}
export OL=${OL:-$S/HDsub/ov}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
ARB=${ARB:-fix}; [ "$ARB" = old ] && export XA_ARB=old || export XA_ARB=fix
J=${JOBS:-2}; T=${TAG:-}
mkdir -p "$HERE/results"
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast indep gb}; do
  i=$W/$s/new; B=${BANDS:-$i/skel_$c.bands.json}; mkdir -p $O/$s
  python3 -I "$X/e8mux/checkbands.py" $B > /dev/null || { echo "$s $c: band file REJECTED"; continue; }
  python3 "$X/events9/cert9.py" $i/skel.json $B $O/$s/cert_${c}_$ARB$T.json ${FLAGS:-} > "$HERE/results/cert9_${s}_${c}_$ARB$T.txt" 2>&1
  ( "$X/events9/xe9.sh" $i/skel.json $B $O/$s/cert_${c}_$ARB$T.json 2>&1 | grep -v '^\[slot\]' > "$HERE/results/xe9_${s}_${c}_$ARB$T.txt" ) &
  while [ "$(jobs -rp | wc -l)" -ge $J ]; do sleep 1; done
done; done
wait
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast indep gb}; do
  f="$HERE/results/xe9_${s}_${c}_$ARB$T.txt"
  echo "$s $c $ARB: $(grep -h 'Back pins' $f | cut -c12-80) | $(grep -h 'guarded pins' $f | cut -c12-60) | $(tail -1 $f | cut -c1-40)"
done; done
