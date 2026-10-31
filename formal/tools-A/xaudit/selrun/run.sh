#!/usr/bin/env bash
# E9SelRun: certsel.py (UNTRUSTED; XA_ARB=old so the nodes are E8Mux's) + xselL (Events9SelLMain.lean,
# lean --run on an olean overlay $OL) on the E8Mux-corrected bands, gcd_hw R5 seeds d 3 4 5 x slow fast gb indep.
#   inputs: $W/<seed>/new/{skel.json, skel_<corner>.bands.json, cert_<corner>.json} (E8Mux), the E8SelC
#           map selhold/results/map_<seed>.json
#   outputs: results/sel_<seed>_<corner>.txt (certsel summary), results/xl_<seed>_<corner>.txt (xselL);
#            certificates in $CD/sel_<seed>_<corner>.json; then table.sh -> results/table.txt
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
S=${S:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad}
W=${W:-$S/e8mux/w}
OL=${OL:-$S/E9SelRun/ov}
CD=${CD:-$S/E9SelRun/w}
MAPD="$HERE/../selhold/results"
export PATH=$HOME/.elan/bin:$PATH PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 XA_ARB=old
mkdir -p "$HERE/results" "$CD"
for s in ${SEEDS:-d 3 4 5}; do
  o=$W/$s/new
  for c in ${CORNERS:-slow fast gb indep}; do
    T=${TAG:-}
    python3 "$HERE/certsel.py" $o/skel.json $o/skel_$c.bands.json $MAPD/map_$s.json $CD/sel_${s}_$c$T.json \
      --ref $o/cert_slow.json ${FLAGS:-} > "$HERE/results/sel_${s}_$c$T.txt" 2>&1
    ( cd /home/user/asyncfpga3/formal/lean && FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c \
      'LEAN_PATH="$0:$LEAN_PATH" exec lean -DautoImplicit=false --run Formal/Core/XAudit/Events9SelLMain.lean "$@"' \
      "$OL" $o/skel.json $o/skel_$c.bands.json $CD/sel_${s}_$c$T.json $MAPD/map_$s.json ) 2>&1 \
      | grep -v '^\[slot\]' > "$HERE/results/xl_${s}_$c$T.txt"
    echo "$s $c$T: $(grep -h 'selL rows' "$HERE/results/xl_${s}_$c$T.txt") | $(tail -3 "$HERE/results/xl_${s}_$c$T.txt" | tr '\n' ' ')"
  done
done
