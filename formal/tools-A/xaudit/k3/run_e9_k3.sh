#!/usr/bin/env bash
# Lead 2026-10-31: the CURRENT routed-timing pipeline (corrected arbiter core) on a K3 kernel:
#   events4/skel.py -> par/cert9p.py (UNTRUSTED) -> xevents9par (Events9ParMain, Events9Par.design_verdict9par)
#                   -> arbnet/gen.py (UNTRUSTED) -> xarbnet (Events9ArbNetMain: ArbOK, OwnOK, RsOK, FixShape,
#                      ArbRowsOK = the checked arbiter premises of Events9FullArb.design_verdict9_full_arb)
#   k3/run_e9_k3.sh <kernel>     SEEDS="d 3 4 5" CORNERS="slow fast indep gb"
# Inputs $OUT/<seed>/{net.json,<corner>.bands.json} (bands_k3.sh). Lean on the overlay $OL via par/xe9p.sh, arbnet/xan.sh.
# Outputs $R/{skel,cert9p,xe9p,gen,xan}_<seed>_<corner>.txt
set -u
K3="$(cd "$(dirname "$0")" && pwd)"; X="$K3/.."
K=$1; OUT=${OUT:-$HOME/k3out/$K}; R=${R:-$K3/out/$K/e9}; J=${JOBS:-2}
export OL=${OL:?set OL to an olean overlay of the Events9ArbNetMain/Events9ParMain closures}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 XA_ARB=fix
mkdir -p "$R"
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast indep gb}; do
  D=$OUT/$s; B=$D/skel_$c.bands.json
  python3 "$X/events4/skel.py" $D/net.json $D/$c.bands.json $D/skel.json $B > "$R/skel_${s}_$c.txt" 2>&1
  python3 -I "$X/e8mux/checkbands.py" $B > /dev/null || { echo "$s $c: band file REJECTED"; continue; }
  python3 "$X/par/cert9p.py" $D/skel.json $B $D/cert9p_$c.json > "$R/cert9p_${s}_$c.txt" 2>&1
  ( "$X/par/xe9p.sh" $D/skel.json $B $D/cert9p_$c.json --fuel ${FUEL:-256} 2>&1 | grep -v '^\[slot\]' > "$R/xe9p_${s}_$c.txt"
    python3 "$X/arbnet/gen.py" $D/skel.json $B $D/cert9p_$c.json $D/arb_$c.json > "$R/gen_${s}_$c.txt" 2>&1
    "$X/arbnet/xan.sh" $D/skel.json $B $D/cert9p_$c.json $D/arb_$c.json --fuel ${FUEL:-256} 2>&1 | grep -v '^\[slot\]' > "$R/xan_${s}_$c.txt" ) &
  while [ "$(jobs -rp | wc -l)" -ge $J ]; do sleep 1; done
done; done
wait
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast indep gb}; do
  echo "$K $s $c: $(tail -1 $R/xe9p_${s}_$c.txt | cut -c1-60) | $(grep -h 'ArbOK and ArbRowsOK' $R/xan_${s}_$c.txt | cut -c11-45)"
done; done
