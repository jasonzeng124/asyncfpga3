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
SPEC=$RS/$SP; [ -f "$SPEC" ] || { echo "$SP | no such spec in RS" | tee "$O/line.txt"; exit 0; }
get() { sed -n "s/^$1=//p" "$SPEC" | head -1; }
K=$(get K); S=$(get SEED); Z=$(get SIZES); TR=$(get TRIMS); WS=$(get SDF); WF=$(get FASM); XE=$(get ENV); M=$(get MLIR)
D=${K}_bench_gen; SM=$O/summary.txt; : > "$SM"; say() { echo "$*" | tee -a "$SM"; }
say "$SP: $K seed $S sdf $WS fasm $WF ENV '$XE' MLIR $M"
V=kernels/$K/vec.hex; [ -f "$RS/$V" ] || V=research/data/suite/vec/$K.hex
if [ -f "$RS/$V" ] && head -1 "$RS/$V" | grep -q '^// benchvec'; then
  [ "$M" = - ] || [ -z "$M" ] || { say "MEM route with an MLIR override: not supported"; echo "$SP | MEM MLIR override: not run" > "$O/line.txt"; exit 0; }
  ( for e in $XE; do export "$e"; done; [ "$TR" = - ] || export TRIM=$RS/$TR
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
grep -q "OK -- sdf" "$O/rebuild.txt" || { echo "$SP | rebuild refused: $(tail -1 "$O/rebuild.txt")" > "$O/line.txt"; exit 0; }
HB2=$BQ_RUNS/hw/bq_${K}_$S; WT=$BQ_RUNS/wt/$BQ_LANE/cells/build; W=$O/hw; mkdir -p "$W/gen"
cp "$HB2/$D.bit" "$HB2/$D.fasm" "$HB2/$D.sdf" "$HB2/${D}_routed.json" "$W/"; cp "$WT/hw/$D/$D.json" "$W/"
cp "$WT/gen/$D.v" "$WT/gen/${K}_kernel_bench.v" "$W/gen/"
PREBUILT=$W bash "$HB/suite/task.sh" "$K" "$S" /dev/null - "$O/t" "$ND" > "$O/task.log" 2>&1
sed 's/^/draws: /' "$O/t/summary.txt" >> "$SM"
echo "$SP | $(grep -o 'OK -- sdf [0-9a-f]*, trimmed fasm [0-9a-f]*' "$O/rebuild.txt") | $(grep -o '^draws K.*' "$O/t/summary.txt" | sed -E 's/^draws K [0-9.]+//' | cut -c1-160 | tr '\n' ';')" > "$O/line.txt"
cat "$O/line.txt"
