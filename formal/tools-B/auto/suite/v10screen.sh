#!/usr/bin/env bash
# tools-B/auto/suite/v10screen.sh SPEC OUT  (shard B, 2026-11-21; UNTRUSTED simulation and extraction, bound logic in Lean)
# One route of a research flow, rebuilt by research's own research/tools/suite/board_rebuild.sh from a spec written by
# mk_specs_all.py (FASM=00000000: no judged fasm, so board_rebuild stops after the sdf check and the trims; the
# trimmed fasm's md5 is reported here and the bit is made with board_rebuild's own fasm2frames / xc7frames2bit lines),
# then racescreen.sh (decode from the bits, 2 + 2 draws, steersafe --auto, ctlsweep, xtol, outsafe) and weaksweep.sh
# (race-only adversary of the weakest steer), all with DRAW_DOUT=23000 (CA_BENCHCAP routes: JOURNAL-B 2026-11-20 13:45).
# MEM=1 specs (mk_specs_all.py --mem): shard C's memtask.sh instead of board_rebuild + racescreen; the structural bound
# and the weakest steer's race-only adversary on the memory boundary (weaksweep.sh with SIMX_EXTRA=--mem).
# Needs RS (research checkout with build/frontend), TC.  Writes OUT/screen.txt (one line).
set -uo pipefail
SPEC=$(readlink -f "$1"); O=$(mkdir -p "$2" && readlink -f "$2"); H=$(cd "$(dirname "$0")/.." && pwd); F=$(cd "$H/../../.." && pwd)
RS=${RS:-/home/user/rs}; export TC=${TC:-$HOME/dev2/lib/fpgatoolchain} RS DRAW_DOUT=${DRAW_DOUT:-23000}
get() { sed -n "s/^$1=//p" "$SPEC" | head -1; }
K=$(get K); S=$(get SEED); NM=$(basename "$SPEC" .spec)
if [ "$(get MEM)" = 1 ]; then   # a memory kernel (benchvec vectors): shard C's memtask.sh builds, trims (TRIM=) and decodes
  # (RAMB18E1 / DSP48E1 too) and runs 1 + 1 of its memory draws; then only steersafe --auto (the race adversaries need
  # the memory boundary, which B's xtol / weaksweep do not drive)
  for e in $(get ENV); do export "$e"; done; TRx=$(get TRIMS); Zx=$(get SIZES)
  case $Zx in formal/*) Zx=$F/$Zx;; esac; case $TRx in formal/*) TRx=$F/$TRx;; esac
  ( [ "$TRx" = - ] || export TRIM=$TRx; TREE=$O/tree bash "$F/formal/tools/margin/bram/memtask.sh" "$K" "$S" "$Zx" "$(get SDF)" "$O/mt" 1 ) > "$O/memtask.txt" 2>&1
  BDm=$O/tree/cells/build/hw/${K}_bench_gen
  fa=$(md5sum < "$BDm/${K}_bench_gen.fasm" 2>/dev/null | cut -c1-8)
  if [ -f "$O/mt/w/m/net.json" ]; then
    timeout 3000 python3 "$H/steersafe.py" "$O/mt/w/m" --auto > "$O/steersafe.txt" 2>&1
    ss=$(grep -o '^steers.*' "$O/steersafe.txt"); w=$(head -1 "$O/steersafe.txt" | cut -c1-28 | tr -s ' ')
    # the weakest steer's race-only adversary on the memory boundary (simx --mem, as C's draws)
    ln -sf v/pairs.txt "$O/mt/pairs.txt"; ln -sf v/exp.txt "$O/mt/exp.txt"; cp "$O/steersafe.txt" "$O/mt/steersafe.txt"
    bash "$H/ensure_m.sh" "$O/mt" > /dev/null 2>&1
    ws=$(SIMX_EXTRA="--mem $O/mt/v/mem.txt --tmax 1900000000" timeout 3000 bash "$H/weaksweep.sh" "$O/mt" "$K" 2>&1 | grep -o 'adversary first failure.*')
  fi
  echo "$NM | MEM | $(grep -o 'sdf [0-9a-f]* (research [0-9a-f]*) [A-Z]*' "$O/mt/summary.txt" | head -1) trimmed fasm ${fa:-?} | draws $(grep -o 'PASS [0-9]* FAIL [0-9]*' "$O/mt/summary.txt" | tr '\n' ' ')| ${ss:-no steersafe: $(tail -1 "$O/mt/summary.txt")} (weakest ${w:-}) | weakest-steer ${ws:-adversary not run}" | tee "$O/screen.txt"
  exit 0
fi
sed -e "s#^SIZES=\(formal/.*\)#SIZES=$F/\1#" -e "s#^TRIMS=\(formal/.*\)#TRIMS=$F/\1#" "$SPEC" > "$O/abs.spec"
# board_rebuild resolves SIZES / TRIMS against the research checkout: give it paths there
mkdir -p "$RS/build/v10screen"; for x in SIZES TRIMS; do v=$(sed -n "s/^$x=//p" "$O/abs.spec"); [ "$v" = - ] || cp "$v" "$RS/build/v10screen/"; done
sed -i -e "s#^SIZES=.*/\([^/]*\)#SIZES=build/v10screen/\1#" -e "s#^TRIMS=/.*/\([^/]*\)#TRIMS=build/v10screen/\1#" "$O/abs.spec"
export BQ_RUNS=${BQ_RUNS:-$O/bq}; D=${K}_bench_gen; HB=$BQ_RUNS/hw/bq_${K}_$S
XZ=${XRAY_DB:-}; [ -n "$XZ" ] && [ -d "$XZ/zynq7" ] && XZ=$XZ/zynq7   # research's xray_delay.py takes the zynq7 directory itself
( cd "$RS" && if [ -n "$XZ" ]; then export XRAY_DB=$XZ; fi; bash research/tools/suite/board_rebuild.sh "$O/abs.spec" ) > "$O/rebuild.txt" 2>&1
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
ws=$(grep -o "race-only adversary: first failure.*" "$O/rs/racescreen.txt" 2>/dev/null | sed 's/race-only adversary: /adversary /')   # racescreen runs weaksweep since 2026-11-21 08:45
[ -n "$ws" ] || ws=$( [ -f "$O/rs/j/w/m/net.json" ] && timeout 3000 bash "$H/weaksweep.sh" "$O/rs/j" "$K" 2>&1 | grep -o 'adversary first failure.*')
echo "$NM | sdf $sdf trimmed fasm $fa | $rs | weakest-steer $ws" | tee "$O/screen.txt"
cp "$O/rs/j/steersafe.txt" "$O/" 2>/dev/null; exit 0
