#!/usr/bin/env bash
# Probe E9Par: par/cert9p.py (UNTRUSTED certificate with parallel-pair lines, corrected arbiter core)
# + xevents9par (lean --run on the overlay $OL, par/xe9p.sh) on the E8Mux corrected bands
# (e8mux/bands.sh: $W/<seed>/new/skel.json, skel_<corner>.bands.json, each passing e8mux/checkbands.py).
#   SEEDS="d 3 4 5"  CORNERS="slow fast indep gb"  TAG=...  FLAGS="--no-par" etc.
# Outputs: results/xe9p_<seed>_<corner><TAG>.txt, results/cert9p_<seed>_<corner><TAG>.txt
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"; X="$HERE/.."
S=${S:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad}
W=${W:-$S/e8mux/w}; O=${O:-$S/E9Par/out}
export OL=${OL:-$S/E9Par/ov2}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 XA_ARB=fix
J=${JOBS:-2}; T=${TAG:-}
mkdir -p "$HERE/results"
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast indep gb}; do
  i=$W/$s/new; B=${BANDS:-$i/skel_$c.bands.json}; mkdir -p $O/$s
  python3 -I "$X/e8mux/checkbands.py" $B > /dev/null || { echo "$s $c: band file REJECTED"; continue; }
  python3 "$HERE/cert9p.py" $i/skel.json $B $O/$s/cert_${c}$T.json ${FLAGS:-} > "$HERE/results/cert9p_${s}_${c}$T.txt" 2>&1
  ( "$HERE/xe9p.sh" $i/skel.json $B $O/$s/cert_${c}$T.json 2>&1 | grep -v '^\[slot\]' > "$HERE/results/xe9p_${s}_${c}$T.txt" ) &
  while [ "$(jobs -rp | wc -l)" -ge $J ]; do sleep 1; done
done; done
wait
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast indep gb}; do
  f="$HERE/results/xe9p_${s}_${c}$T.txt"
  echo "$s $c: $(grep -h 'parallel-pair' $f | cut -c15-90) | $(grep -h 'Back pins' $f | cut -c15-80) | $(grep -h 'guarded pins' $f | cut -c15-60) | $(tail -1 $f | cut -c1-40)"
done; done
