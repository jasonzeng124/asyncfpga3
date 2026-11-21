#!/usr/bin/env bash
# tools-B/auto/suite/v10screen.sh SPEC OUT  (shard B, 2026-11-21; UNTRUSTED simulation and extraction, bound logic in Lean)
# One route of a research flow, rebuilt by research's own research/tools/suite/board_rebuild.sh from a spec written by
# mk_specs_all.py (FASM=00000000: no judged fasm, so board_rebuild stops after the sdf check and the trims; the
# trimmed fasm's md5 is reported here and the bit is made with board_rebuild's own fasm2frames / xc7frames2bit lines),
# then racescreen.sh (decode from the bits, 2 + 2 draws, steersafe --auto, ctlsweep, xtol, outsafe) and weaksweep.sh
# (race-only adversary of the weakest steer), all with DRAW_DOUT=23000 (CA_BENCHCAP routes: JOURNAL-B 2026-11-20 13:45).
# Needs RS (research checkout with build/frontend), TC.  Writes OUT/screen.txt (one line).
set -uo pipefail
SPEC=$(readlink -f "$1"); O=$(mkdir -p "$2" && readlink -f "$2"); H=$(cd "$(dirname "$0")/.." && pwd); F=$(cd "$H/../../.." && pwd)
RS=${RS:-/home/user/rs}; export TC=${TC:-$HOME/dev2/lib/fpgatoolchain} RS DRAW_DOUT=${DRAW_DOUT:-23000}
get() { sed -n "s/^$1=//p" "$SPEC" | head -1; }
K=$(get K); S=$(get SEED); NM=$(basename "$SPEC" .spec)
sed -e "s#^SIZES=\(formal/.*\)#SIZES=$F/\1#" -e "s#^TRIMS=\(formal/.*\)#TRIMS=$F/\1#" "$SPEC" > "$O/abs.spec"
# board_rebuild resolves SIZES / TRIMS against the research checkout: give it paths there
mkdir -p "$RS/build/v10screen"; for x in SIZES TRIMS; do v=$(sed -n "s/^$x=//p" "$O/abs.spec"); [ "$v" = - ] || cp "$v" "$RS/build/v10screen/"; done
sed -i -e "s#^SIZES=.*/\([^/]*\)#SIZES=build/v10screen/\1#" -e "s#^TRIMS=/.*/\([^/]*\)#TRIMS=build/v10screen/\1#" "$O/abs.spec"
export BQ_RUNS=${BQ_RUNS:-$O/bq}; D=${K}_bench_gen; HB=$BQ_RUNS/hw/bq_${K}_$S
( cd "$RS" && bash research/tools/suite/board_rebuild.sh "$O/abs.spec" ) > "$O/rebuild.txt" 2>&1
if ! grep -q "trimmed fasm .* not 00000000" "$O/rebuild.txt"; then echo "$NM | rebuild: $(tail -1 "$O/rebuild.txt")" | tee "$O/screen.txt"; exit 0; fi
fa=$(md5sum < "$HB/$D.fasm" | cut -c1-8); sdf=$(md5sum < "$HB/$D.sdf" | cut -c1-8)
P=xc7z010clg400-1; DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PX=$TC/openxc7-src/prjxray
PYTHONPATH="$PX:$TC/openxc7/lib/python" python3 "$PX/utils/fasm2frames.py" --db-root "$DB" --part "$P" "$HB/$D.fasm" > "$HB/$D.frames" 2> "$HB/frames.log" &&
"$TC/openxc7/bin/xc7frames2bit" --part_file "$DB/$P/part.yaml" --part_name "$P" --frm_file "$HB/$D.frames" --output_file "$HB/$D.bit" > "$HB/bit.log" 2>&1 ||
  { echo "$NM | bitstream FAILED" | tee "$O/screen.txt"; exit 0; }
W=$O/hw; mkdir -p "$W/gen"; WT=$BQ_RUNS/wt/${BQ_LANE:-bq}/cells/build
cp "$HB/$D.bit" "$HB/$D.fasm" "$HB/$D.sdf" "$HB/${D}_routed.json" "$W/"; cp "$WT/hw/$D/$D.json" "$W/"
cp "$WT/gen/$D.v" "$WT/gen/${K}_kernel_bench.v" "$W/gen/"
rs=$(bash "$H/racescreen.sh" "$K" "$W" "$O/rs" 2>&1 | tail -1)
ws=$( [ -f "$O/rs/j/w/m/net.json" ] && timeout 6000 bash "$H/weaksweep.sh" "$O/rs/j" "$K" 2>&1 | grep -o 'adversary first failure.*')
echo "$NM | sdf $sdf trimmed fasm $fa | $rs | weakest-steer $ws" | tee "$O/screen.txt"
cp "$O/rs/j/steersafe.txt" "$O/" 2>/dev/null; exit 0
