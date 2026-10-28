#!/usr/bin/env bash
# Controlled version of the ucmpi1 shmoo.
#
# Two things the pilot got wrong:
#   1. BD_SIZES_GATE=0 SKIPS the block that writes tighten_gate.log, so every
#      margin it logged was a stale copy of the previous build's.  Here
#      tighten.py is run directly against each build's OWN routed SDF, so the
#      margin and the bitstream the board judges are the same route.
#   2. build_bench.sh retries PnR on a fresh seed when a build misses timing
#      (build_bench.sh:372), and this harness only just closes 83 MHz -- so
#      points were landing on different seeds and the route moved for reasons
#      that had nothing to do with the link count.  NEXTPNR_SEED pins it.
# This still deliberately builds rule-A violations, so the gate stays off and
# every bitstream here is a broken measurement artifact that must never ship.
set -u
cd "$(dirname "$0")/.."
D=${D:-${TMPDIR:-/tmp}/shmoo}
mkdir -p "$D"
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
export NEXTPNR_SEED=1
GOLD_SIG=0x03dba483; GOLD_ODATA=2863579695
TSV="$D/results2.tsv"
printf 'n\tlinks\tchain_ps\tps_link\treq\tpeak\tguard\tmargin\tslack\tworst\tw_margin\tw_slack\tnviol\tverdict\tsig\tcycles\tlatmin\tlatmax\n' > "$TSV"
mkdir -p "$D/bit2" "$D/logs2"

for f in "$D"/sizes/*.vh; do
    n=$(grep UCMPI1 "$f" | awk '{print $3}')
    tag=$(basename "$f" .vh)
    echo "########## $tag  (ucmpi1 = $n links, seed $NEXTPNR_SEED) ##########"
    if ! BD_SIZES="$f" BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 timeout 1800 \
         hw/build_bench.sh xorshift > "$D/logs2/build_$tag.log" 2>&1; then
        echo "  BUILD FAILED"; printf '%s\tBUILDFAIL\n' "$n" >> "$TSV"; continue
    fi
    O=build/hw/xorshift_bench_gen
    cp "$O/xorshift_bench_gen.bit" "$D/bit2/$tag.bit"
    python3 verify/tighten.py "$O/xorshift_bench_gen.sdf" > "$D/logs2/tighten_$tag.log" 2>&1 || true

    read -r LI CH PS RQ PK GD MG SL WC WM WS NV <<<"$(python3 - "$D/logs2/tighten_$tag.log" <<'PY'
import re, sys
txt = open(sys.argv[1]).read()
sec = txt.split("\nA. ", 1)[1].split("\nB. ", 1)[0]
rows = []
for m in re.finditer(r"^  (\S+)\s+(\d+) links\s+(\d+) ps\s+req\s+(-?\d+)\s+peak\s+(-?\d+)\s+guard\s+(\d+)\s+margin\s+(-?\d+)(.*)$", sec, re.M):
    c, li, ch, rq, pk, g, mg, tl = m.groups()
    rows.append(dict(cell=c.split(".")[-1], links=int(li), chain=int(ch), req=int(rq),
                     peak=int(pk), guard=int(g), margin=int(mg), viol="VIOLATION" in tl))
w = min(rows, key=lambda r: r["margin"])
c = [r for r in rows if r["cell"] == "ucmpi1"][0]
print(c["links"], c["chain"], c["chain"]//max(1,c["links"]), c["req"], c["peak"],
      c["guard"], c["margin"], c["margin"]+c["guard"], w["cell"], w["margin"],
      w["margin"]+w["guard"], sum(r["viol"] for r in rows))
PY
)"
    echo "  model: ucmpi1 $LI links $CH ps ($PS/link) req $RQ peak $PK guard $GD margin $MG slack $SL"
    echo "         worst cell $WC margin $WM slack $WS | $NV rule-A violation(s)"

    if timeout 900 hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$D/bit2/$tag.bit" \
         xorshift 2000 0x00100C00 > "$D/logs2/run_$tag.log" 2>&1; then V=PASS; else V=FAIL; fi
    L="$D/logs2/run_$tag.log"
    SIG=$(grep -o 'sig=0x[0-9a-f]*' "$L" | head -1 | cut -d= -f2)
    CY=$(grep -o 'cycles=[0-9]*' "$L" | head -1 | cut -d= -f2)
    LMIN=$(grep -o 'latmin=[0-9]*' "$L" | head -1 | cut -d= -f2)
    LMAX=$(grep -o 'latmax=[0-9]*' "$L" | head -1 | cut -d= -f2)
    OD=$(grep -o 'odata=[0-9]*' "$L" | head -1 | cut -d= -f2)
    [ "$V" = PASS ] && [ -n "${SIG:-}" ] && [ "$SIG" != "$GOLD_SIG" ] && V=WRONGSIG
    [ "$V" = PASS ] && [ -n "${OD:-}" ] && [ "$OD" != "$GOLD_ODATA" ] && V=WRONGDATA
    echo "  board: $V  sig=${SIG:--} cycles=${CY:--} lat=${LMIN:--}/${LMAX:--}"
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$n" "$LI" "$CH" "$PS" "$RQ" "$PK" "$GD" "$MG" "$SL" "$WC" "$WM" "$WS" "$NV" \
      "$V" "${SIG:--}" "${CY:--}" "${LMIN:--}" "${LMAX:--}" >> "$TSV"
done
echo "########## SWEEP2 DONE ##########"
column -t "$TSV"
