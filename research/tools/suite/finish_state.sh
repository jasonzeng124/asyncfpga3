#!/usr/bin/env bash
# finish_state.sh STATE DEST -- a sizing loop's files (research/tools/auto/auto_size.sh's $RUNS/auto/NAME, or a farm
# task's auto/ copy) cut back to the START of its finish phase, for auto_size.sh AUTO_RESUME=DEST: every file of the
# iterations <= P2-1 (the last phase-1 route, whose raise-only ratchet wrote sizes_P2), sizes_P2.vh, pinned_P2-1 as
# pinned.txt, and log.txt up to its "phase 2 (raise-only) from it P2" line. The resumed loop then builds route P2 first,
# from the same sizes on the same seed: the original loop's own route P2 (its sdf md5 is in STATE/it_P2.txt), so the
# original run is the control of whatever the resumed finish phase changes (subagent converge: AUTO_FINISH_SEEDS).
# Prints one line: P2, the number of files, the last log line.
set -euo pipefail
T=$1; D=$2
p2=$(grep -o '^phase 2 (raise-only) from it [0-9]*' "$T/log.txt" | head -1 | grep -o '[0-9]*$')
[ -n "$p2" ] || { echo "finish_state: $T/log.txt has no phase-2 line" >&2; exit 1; }
last=$((p2 - 1)); mkdir -p "$D"
for f in "$T"/*.txt "$T"/*.vh; do
  b=$(basename "$f")
  case $b in result.txt|sizes_final.vh|log.txt|pinned.txt) continue;; esac
  n=$(echo "$b" | sed -n 's/^[a-z_]*_\([0-9]\+\)\(s[0-9]\+\)\?\([._].*\)$/\1/p')   # it_5s1.txt: AUTO_FINISH_SEEDS
  if [ -z "$n" ]; then cp "$f" "$D/"; continue; fi             # sizes_est.vh
  if [ "$n" -le "$last" ] || [ "$b" = "sizes_$p2.vh" ]; then cp "$f" "$D/"; fi
done
sed "/^phase 2 (raise-only) from it $p2\$/q" "$T/log.txt" > "$D/log.txt"
cp "$D/pinned_$last.txt" "$D/pinned.txt" 2>/dev/null || true
echo "finish_state: P2=$p2, $(ls "$D" | wc -l) files, log ends: $(tail -1 "$D/log.txt")"
