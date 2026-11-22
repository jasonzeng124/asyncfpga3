#!/usr/bin/env bash
# margin/spec/drawspec.sh SPEC OUT [NDRAWS]  (shard C, 2026-11-22; UNTRUSTED simulation): formal's board approximator on
# one route named by a research board spec (research/data/suite/board/**/*.spec: K, SEED, SIZES, TRIMS, MLIR, ENV, SDF,
# FASM).  SPEC is a path inside $RS (research checkout).  Non-memory kernels: research's own board_rebuild.sh rebuilds the
# route and refuses unless the sdf AND the trimmed fasm are the judged ones; the bits are read back (bit2fasm), decoded
# and NDRAWS (default 64) draws of research's delay model plus NDRAWS slow-carry draws (CARRY4 / F7F8 / FF in [0.8, 1.0])
# are run on the kernel's own vectors (tools-B/auto/suite/task.sh PREBUILT=, DRAW_DOUT=23000 as research's PS bench).
# Memory kernels (benchvec vectors): margin/bram/memtask.sh with the spec's ENV and TRIMS (its own sdf check; the trimmed
# fasm md5 is compared here with the spec's FASM).  OUT/summary.txt; one line in OUT/line.txt.
set -uo pipefail
SP=$1; O=$(mkdir -p "$2" && readlink -f "$2"); ND=${3:-64}
RS=${RS:-/home/user/rs}; export RS TC=${TC:-$HOME/dev2/lib/fpgatoolchain} DRAW_DOUT=${DRAW_DOUT:-23000}
F=$(cd "$(dirname "$0")/../../../.." && pwd); HB=$F/formal/tools-B/auto
# a spec in this checkout (formal/..., e.g. shard B's mk_specs_all.py output with FASM=00000000: no judged fasm, the
# trimmed fasm's md5 is reported and the bit made here as tools-B v10screen.sh does): SIZES / TRIMS copied into $RS
case $SP in formal/*)
  mkdir -p "$RS/build/dspec"; A=$RS/build/dspec/$(basename "$SP")
  sed -e "s#^SIZES=\(formal/.*\)#SIZES=$F/\1#" -e "s#^TRIMS=\(formal/.*\)#TRIMS=$F/\1#" "$F/$SP" > "$A"
  for x in SIZES TRIMS; do v=$(sed -n "s/^$x=//p" "$A"); case $v in /*) cp "$v" "$RS/build/dspec/";; esac; done
  sed -i -e "s#^SIZES=/.*/\([^/]*\)#SIZES=build/dspec/\1#" -e "s#^TRIMS=/.*/\([^/]*\)#TRIMS=build/dspec/\1#" "$A"
  SP=build/dspec/$(basename "$SP");;
esac
SPEC=$RS/$SP; [ -f "$SPEC" ] || { echo "$SP | no such spec in RS" | tee "$O/line.txt"; exit 0; }
get() { sed -n "s/^$1=//p" "$SPEC" | head -1; }
K=$(get K); S=$(get SEED); Z=$(get SIZES); TR=$(get TRIMS); WS=$(get SDF); WF=$(get FASM); XE=$(get ENV); M=$(get MLIR)
D=${K}_bench_gen; SM=$O/summary.txt; : > "$SM"; say() { echo "$*" | tee -a "$SM"; }
say "$SP: $K seed $S sdf $WS fasm $WF ENV '$XE' MLIR $M"
V=kernels/$K/vec.hex; [ -f "$RS/$V" ] || V=research/data/suite/vec/$K.hex
if [ -f "$RS/$V" ] && head -1 "$RS/$V" | grep -q '^// benchvec'; then
  [ "$M" = - ] || [ -z "$M" ] || { say "MEM route with an MLIR override: not supported"; echo "$SP | MEM MLIR override: not run" > "$O/line.txt"; exit 0; }
  ( export HOSTPORT=${HOSTPORT-1}; for e in $XE; do export "$e"; done; [ "$TR" = - ] || export TRIM=$RS/$TR
    TREE=$O/tree bash "$F/formal/tools/margin/bram/memtask.sh" "$K" "$S" "$RS/$Z" "$WS" "$O/mt" "$ND" ) > "$O/memtask.log" 2>&1
  sed 's/^/mem: /' "$O/mt/summary.txt" >> "$SM"
  fa=$(md5sum < "$O/tree/cells/build/hw/$D/$D.fasm" 2>/dev/null | cut -c1-8)
  rf=$(grep -c '^REFUSED' "$O/mt/trim.log" 2>/dev/null); say "trimmed fasm $fa (spec $WF) $([ "$fa" = "$WF" ] && echo SAME || echo DIFFERENT); trim REFUSED lines ${rf:-0}"
  echo "$SP | MEM | $(grep -o 'sdf [0-9a-f]* (research [0-9a-f]*) [A-Z]*' "$O/mt/summary.txt" | head -1) | fasm $fa $([ "$fa" = "$WF" ] && echo SAME || echo DIFFERENT) | $(grep -o 'draws K.*pass fraction [0-9.]*' "$O/mt/summary.txt" | sed 's/draws K [0-9.]*//' | tr '\n' ';')" > "$O/line.txt"
  cat "$O/line.txt"; exit 0
fi
export BQ_RUNS=$O/bq BQ_LANE=${BQ_LANE:-dsc}
# lane2.sh copies $RS/build/frontend (a research sandbox has it; a bare checkout, e.g. the farm's PEER, does not)
[ -d "$RS/build/frontend" ] || { mkdir -p "$RS/build"; cp -r "$RS/cloud/fixtures/frontend" "$RS/build/"; }
XZ=${XRAY_DB:-}; [ -n "$XZ" ] && [ -d "$XZ/zynq7" ] && XZ=$XZ/zynq7
( cd "$RS" && if [ -n "$XZ" ]; then export XRAY_DB=$XZ; fi; bash research/tools/suite/board_rebuild.sh "$SPEC" ) > "$O/rebuild.txt" 2>&1
say "rebuild: $(tail -1 "$O/rebuild.txt")"
HB2=$BQ_RUNS/hw/bq_${K}_$S
if [ "$WF" = 00000000 ] && grep -q "trimmed fasm .* not 00000000" "$O/rebuild.txt"; then   # no judged fasm: make the bit here
  P=xc7z010clg400-1; DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PX=$TC/openxc7-src/prjxray
  PYTHONPATH="$PX:$TC/openxc7/lib/python" python3 "$PX/utils/fasm2frames.py" --db-root "$DB" --part "$P" "$HB2/$D.fasm" > "$HB2/$D.frames" 2> "$HB2/frames.log" &&
  "$TC/openxc7/bin/xc7frames2bit" --part_file "$DB/$P/part.yaml" --part_name "$P" --frm_file "$HB2/$D.frames" --output_file "$HB2/$D.bit" > "$HB2/bit.log" 2>&1 &&
  echo "OK -- sdf $(md5sum < "$HB2/$D.sdf" | cut -c1-8), trimmed fasm $(md5sum < "$HB2/$D.fasm" | cut -c1-8) (no judged fasm in the spec; bit made by drawspec)" >> "$O/rebuild.txt"
fi
grep -q "OK -- sdf" "$O/rebuild.txt" || { echo "$SP | rebuild refused: $(tail -1 "$O/rebuild.txt")" > "$O/line.txt"; exit 0; }
WT=$BQ_RUNS/wt/$BQ_LANE/cells/build; W=$O/hw; mkdir -p "$W/gen"
cp "$HB2/$D.bit" "$HB2/$D.fasm" "$HB2/$D.sdf" "$HB2/${D}_routed.json" "$W/"; cp "$WT/hw/$D/$D.json" "$W/"
cp "$WT/gen/$D.v" "$WT/gen/${K}_kernel_bench.v" "$W/gen/"
PREBUILT=$W bash "$HB/suite/task.sh" "$K" "$S" /dev/null - "$O/t" "$ND" > "$O/task.log" 2>&1
sed 's/^/draws: /' "$O/t/summary.txt" >> "$SM"
echo "$SP | $(grep -o 'OK -- sdf [0-9a-f]*, trimmed fasm [0-9a-f]*' "$O/rebuild.txt") | $(grep -o '^draws K.*' "$O/t/summary.txt" | sed -E 's/^draws K [0-9.]+//' | cut -c1-160 | tr '\n' ';')" > "$O/line.txt"
cat "$O/line.txt"
