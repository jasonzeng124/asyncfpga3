#!/usr/bin/env bash
# Probe E9ArbNet: arbnet/gen.py (UNTRUSTED arbiter data) + xarbnet (lean --run on the overlay $OL, arbnet/xan.sh)
# on the E8Mux corrected bands and E9Par's certificates (par/run.sh outputs $S/E9Par/out/<seed>/cert_<corner>.json).
#   SEEDS="d 3 4 5"  CORNERS="slow fast indep gb"  TAG=...  GENFLAGS=...
# Outputs: results/xan_<seed>_<corner><TAG>.txt, $O/<seed>/arb_<corner><TAG>.json
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"; X="$HERE/.."
S=${S:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad}
W=${W:-$S/e8mux/w}; CD=${CD:-$S/E9Par/out}; O=${O:-$S/E9ArbNet/out}
export OL=${OL:-$S/E9ArbNet/ov}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 XA_ARB=fix
J=${JOBS:-2}; T=${TAG:-}
mkdir -p "$HERE/results"
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast indep gb}; do
  i=$W/$s/new; B=${BANDS:-$i/skel_$c.bands.json}; C=${CERT:-$CD/$s/cert_$c.json}; mkdir -p $O/$s
  python3 -I "$X/e8mux/checkbands.py" $B > /dev/null || { echo "$s $c: band file REJECTED"; continue; }
  python3 "$HERE/gen.py" $i/skel.json $B $C $O/$s/arb_${c}$T.json ${GENFLAGS:-} > "$HERE/results/gen_${s}_${c}$T.txt" 2>&1
  ( "$HERE/xan.sh" $i/skel.json $B $C $O/$s/arb_${c}$T.json 2>&1 | grep -v '^\[slot\]' > "$HERE/results/xan_${s}_${c}$T.txt" ) &
  while [ "$(jobs -rp | wc -l)" -ge $J ]; do sleep 1; done
done; done
wait
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast indep gb}; do
  f="$HERE/results/xan_${s}_${c}$T.txt"
  echo "$s $c: $(grep -h 'ArbOK [0-9]' $f | cut -c11-) | $(tail -1 $f | cut -c1-30)"
done; done
