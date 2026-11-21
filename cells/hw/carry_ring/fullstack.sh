#!/usr/bin/env bash
# The full stack on one carry_ro_top build, before any board run:
#   1. xray_delay.py: prjxray (FAST_MIN : SLOW_MIN : SLOW_MAX) SDF of the route
#   2. fasm2net.py --bit: the netlist the BOARD runs, decoded from the .bit,
#      with that SDF re-keyed onto it
#   3. fasm_equiv.py: decoded netlist vs routed JSON (must be EQUIVALENT);
#      check_chains.py: the carry chains / MUXF7 stages are in the bits
#      (chain lengths, sites, S pins, carry-in)
#   4. carry_predict.py --check-gen: per-ring P = LO + x R + yc C + yf F
#      (predicted.tsv), cross-checked against gen.py's own SDF reading
#   5. (GLS=1) carry_gls.sh: event GLS of group 0 on the decoded netlist at
#      FAST_MIN, SLOW_MAX and band points; gls.tsv
#
#   cells/hw/carry_ring/fullstack.sh BUILDDIR
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
CELLS=$(cd "$HERE/../.." && pwd)
H=$(cd "$1" && pwd)
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
export PYTHONPATH="$TC/openxc7-src/prjxray:$TC/openxc7/lib/python${PYTHONPATH:+:$PYTHONPATH}"
export XRAY_DB=${XRAY_DB:-/root/dev2/lib/xray/prjxray-db/zynq7}
T=carry_ro_top

echo "== xray_delay =="
# rc 2 = some routing element did not resolve; known here: a CO3->CIN link
# across the Y49/Y50 clock-region boundary (prjxray has no node for it, the arc
# keeps nextpnr's 110 ps).  carry_predict flags such rings 'nonxray' and the
# fit leaves them out; anything else unresolved is fatal.
set +e
python3 "$CELLS/gls/fid/xray_delay.py" --routed "$H/${T}_routed.json" --sdf "$H/$T.sdf" \
    --out "$H/xray.sdf" --arcs "$H/xray_arcs.tsv" > "$H/xray.log" 2>&1
rc=$?
set -e
tail -1 "$H/xray.log"
awk -F'\t' 'NR>1{print $11}' "$H/xray_arcs.tsv" | sort | uniq -c | tr '\n' ' '; echo
if [ $rc != 0 ]; then
    unres=$(awk -F'\t' 'NR>1 && $11!="ok" && $11!="nosink" && !($2 ~ /\/CO3$/ && $3 ~ /\/CIN$/)' "$H/xray_arcs.tsv" | grep -c . || true)
    echo "xray_delay rc $rc; unresolved arcs other than CO3->CIN links: $unres"
    [ "$unres" = 0 ] || exit 1
fi

echo "== fasm2net (from the .bit) =="
python3 "$CELLS/gls/fid/fasm2net.py" --bit "$H/$T.bit" --out "$H/fid" \
    --names "$H/${T}_routed.json" --sdf "$H/xray.sdf" > "$H/fasm2net.log" 2>&1
grep -E "^cells:" "$H/fasm2net.log"
echo "== fasm_equiv =="
python3 "$CELLS/gls/fid/fasm_equiv.py" "$H/${T}_routed.json" "$H/fid/fasm_routed.json" \
    "$H/fid/routes.tsv" "$H/fid/stubs.tsv" --out "$H/equiv.txt" --max 3 | grep -E "^[0-9]\.|VERDICT"
grep -q "VERDICT: EQUIVALENT" "$H/equiv.txt" || { echo "NOT EQUIVALENT"; exit 1; }

echo "== carry chains / MUXF7 stages in the decoded bits =="
python3 "$HERE/check_chains.py" "$H/${T}_routed.json" "$H/fid/fasm_routed.json"

echo "== carry_predict =="
python3 "$HERE/carry_predict.py" "$H/xray.sdf" --check-gen > "$H/predicted.tsv"
python3 "$HERE/carry_predict.py" --summary "$H/predicted.tsv"

if [ "${GLS:-0}" = 1 ]; then
    echo "== event GLS of group 0, decoded netlist =="
    printf "field\tx\ty\tslot\tperiod_ps\tedges\n" > "$H/gls.tsv"
    for pt in "min - -" "max - -" "band 0.288 0.2" "band 0.288 0.6" "band 0.288 1.0" "band 0.22 0.2"; do
        set -- $pt
        "$HERE/carry_gls.sh" "$H/fid" "$H/gls_work" "$1" "$2" "$3" > "$H/gls_last.log" 2>&1 || { cat "$H/gls_last.log"; exit 1; }
        grep "^RING" "$H/gls_last.log" | awk -v f="$1" -v x="$2" -v y="$3" '{print f"\t"x"\t"y"\t"$2"\t"$3"\t"$4}' >> "$H/gls.tsv"
        echo "  $pt done"
    done
    rm -rf "$H/gls_work"
    python3 "$HERE/carry_predict.py" --compare-gls "$H/predicted.tsv" "$H/gls.tsv"
fi
echo "fullstack.sh PASS"
