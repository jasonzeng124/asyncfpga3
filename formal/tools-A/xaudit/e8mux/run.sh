#!/usr/bin/env bash
# E8Mux step 3: cert8.py (UNTRUSTED certificate, events8/) + xevents8 on the band files of bands.sh.
#   ROWS="d:new:gb 3:new:slow ..." (seed:variant:corner); default = new x {d,3,4,5} x {slow,fast,indep,gb}
# Every band file passes checkbands.py first (lo > hi rejected).  Outputs: results/xe_<seed>_<variant>_<corner>.txt
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"; X="$HERE/.."
S=${S:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/e8mux}; W=${W:-$S/w}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
J=${JOBS:-1}
mkdir -p "$HERE/results"
if [ -z "${ROWS:-}" ]; then ROWS=""; for s in d 3 4 5; do for c in slow fast indep gb; do ROWS="$ROWS $s:new:$c"; done; done; fi
for r in $ROWS; do
  IFS=: read s v c <<< "$r"; o=$W/$s/$v; B=${BANDS:-$o/skel_$c.bands.json}; T=${TAG:-}
  python3 -I "$HERE/checkbands.py" $B > /dev/null || { echo "$r: band file REJECTED"; continue; }
  python3 "$X/events8/cert8.py" $o/skel.json $B $o/cert_$c$T.json ${FLAGS:-} > "$HERE/results/cert_${s}_${v}_$c$T.txt" 2>&1
  ( "$HERE/xe.sh" $o/skel.json $B $o/cert_$c$T.json 2>&1 | grep -v '^\[slot\]' > "$HERE/results/xe_${s}_${v}_$c$T.txt" ) &
  while [ "$(jobs -rp | wc -l)" -ge $J ]; do sleep 1; done
done
wait
for r in $ROWS; do IFS=: read s v c <<< "$r"; f="$HERE/results/xe_${s}_${v}_$c${TAG:-}.txt"
  echo "$r: $(grep -h 'guarded pins' $f | cut -c12-140) | $(tail -1 $f | cut -c1-40)"; done
