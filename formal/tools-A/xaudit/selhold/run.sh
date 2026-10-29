#!/usr/bin/env bash
# E8SelC: select map (mkmap.py, UNTRUSTED) + xselhold (Events9SelMain.lean, lean --run on an olean
# overlay $OL) on the E8Mux-corrected bands, gcd_hw R5 seeds d 3 4 5 x slow fast gb indep.
#   inputs: $W/<seed>/new/{skel.json, skel_<corner>.bands.json, cert_<corner>.json, net.json}
#           (tools-A/xaudit/e8mux/bands.sh + run.sh outputs; cert = cert8.py on that band file)
#   outputs: results/map_<seed>.json, results/xs_<seed>_<corner>.txt, results/table.txt
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
S=${S:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad}
W=${W:-$S/e8mux/w}
OL=${OL:-$S/E8SelC/ov}
MAPD=/home/user/asyncfpga3/formal/lean/Formal/Cells/ResetCapstoneMapData.lean
export PATH=$HOME/.elan/bin:$PATH PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
mkdir -p "$HERE/results"
for s in ${SEEDS:-d 3 4 5}; do
  o=$W/$s/new
  # the map depends on the netlist and the certificate's node list (same nodes on every corner:
  # checked below by comparing the node names of the four certificates)
  python3 -I "$HERE/mkmap.py" $o/cert_slow.json $o/skel.json $o/net.json $MAPD "$HERE/results/map_$s.json" \
    > "$HERE/results/mkmap_$s.txt" 2>&1
  for c in ${CORNERS:-slow fast gb indep}; do
    python3 -I -c "import json,sys; a=[n['name'] for n in json.load(open(sys.argv[1]))['nodes']]; b=[n['name'] for n in json.load(open(sys.argv[2]))['nodes']]; sys.exit(0 if a==b else 1)" \
      $o/cert_slow.json $o/cert_$c.json || { echo "$s $c: certificate nodes differ from slow: map not valid"; continue; }
    ( cd /home/user/asyncfpga3/formal/lean && FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c \
      'LEAN_PATH="$0:$LEAN_PATH" exec lean -DautoImplicit=false --run Formal/Core/XAudit/Events9SelMain.lean "$@"' \
      "$OL" $o/skel.json ${BANDS:-$o/skel_$c.bands.json} $o/cert_$c.json "$HERE/results/map_$s.json" ) 2>&1 \
      | grep -v '^\[slot\]' > "$HERE/results/xs_${s}_$c${TAG:-}.txt"
    echo "$s $c: $(grep -h '^\[xselhold\] literals' "$HERE/results/xs_${s}_$c${TAG:-}.txt") | $(tail -1 "$HERE/results/xs_${s}_$c${TAG:-}.txt")"
  done
done
