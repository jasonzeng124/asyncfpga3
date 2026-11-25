#!/usr/bin/env bash
# tools-B/auto/suite/preload.sh DIR K LINK I0 "a,n ..." NDRAWS K0 [XBAND]  (shard B, UNTRUSTED simulation): the loop counter
# of a counted-loop suite kernel (countloop / horner / brhash / varshift) started at I0 through its entry link LINK (whose
# latches hold the constant 0 in every ordinary run) on the decoded route DIR/w/m (task.sh's output), NDRAWS draws from K0
# with the oracle from the same state (ploracle.py). Prints draws.py's line and the NEARMISS sum.
set -uo pipefail
D=$1; K=$2; L=$3; I0=$4; P=$5; N=$6; K0=$7; X=${8:-}; H=$(cd "$(dirname "$0")/.." && pwd); S=$(cd "$(dirname "$0")" && pwd)
M=$D/w/m; O=$D/pre_${I0}${X:+_x}; mkdir -p "$O"
python3 "$H/../preload/preload_net.py" "$M/net.json" "$M/routed.json" "$O/net.json" --link "$L" --value "$I0" > "$O/preload.txt" 2>&1 || { cat "$O/preload.txt"; exit 1; }
cp "$M/bnd.json" "$O/"
python3 "$S/ploracle.py" "$K" "$I0" $P > "$O/exp.txt" || exit 1
DRAW_XBAND=$X python3 "$H/xdraws.py" "$O/exp.txt" "$O/net.json" "$O/bnd.json" "$O/d" --kernel "$K" --pairs $P --draws "$N" --seed0 "$K0" \
  --jobs ${JOBS:-3} --routed "$M/routed.json" --tmax 400000000 > "$O/log.txt" 2>&1
echo "$K preload $L=$I0${X:+ slow-carry}: $(grep '^draws [0-9]' "$O/log.txt") | nearmiss $(grep -o 'nearmiss [0-9]*' "$O/d/draws.txt" | awk '{s+=$2} END{print s+0}') $(grep -E 'seed [0-9]+ (FAIL|UND)' "$O/log.txt" | cut -c1-200 | tr '\n' ' ')"
rm -f "$O/net.json" "$O/d/net.simx" "$O/d/simx"
