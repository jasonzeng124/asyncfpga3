#!/usr/bin/env bash
# overbuild_farm.sh REQ TASK OUTROOT H [ENV...] -- a farm loop that ended NOT CLEAN, its finish phase run again here with
# AUTO_OVERBUILD=H (auto_size.sh: every trimmable line built H elements longer at the switch, a route clean when the
# trim step alone makes it so, the shipped route trimmed): the task's auto/ files up to iteration MAXIT-1 (the farm's
# own phase 1), so iteration MAXIT is rebuilt here from the farm's sizes and seed (its sdf md5 is checked against the
# farm's it_MAXIT.txt in the log) and the switch to the finish phase happens on a local route; then the finish phase,
# the full stack, and suite_one.sh's draws on the farm's own draw points.  AUTO_SEARCH=0 (the farm's NOT CLEAN loops
# shipped their least-short route; the search phase is not what is compared).  The control is the farm's own finish
# phase on the same phase-1 state.  ENV: the request's environment (CA_BENCHCAP=1 for suite13 / exit1).  Run it from a
# checkout whose build/frontend holds the request's fixtures.  Writes OUTROOT/REQ_TASK_obH/; prints one line.
set -uo pipefail
Q=$1; TK=$2; OR=$(mkdir -p "$3" && cd "$3" && pwd); H=$4; shift 4
MAXIT=${MAXIT:-4}
R=$(cd "$(dirname "$0")/../../.." && pwd)
W=$OR/${Q}_${TK}_ob$H; rm -rf "$W"; mkdir -p "$W/farm"
git -C "$R" archive origin/claude/cluster "results/$Q/$TK" 2>/dev/null | tar -x -C "$W/farm" --strip-components=3 \
  || { echo "$Q $TK | no farm files"; exit 1; }
read -r _ _ K _ S _ <<< "$(head -1 "$W/farm/task.txt")"
export RUNS=$W/runs; mkdir -p "$RUNS"
A=$RUNS/farm_auto; mkdir -p "$A"
# phase 1 as the farm ran it, up to iteration MAXIT-1; sizes_MAXIT (that iteration's ratchet output) and its seed
for f in "$W"/farm/auto/*; do
  b=$(basename "$f"); n=$(echo "$b" | sed -n 's/^[a-z]*_\([0-9]*\)[._].*/\1/p')
  case $b in sizes_est.vh|pinned.txt) cp "$f" "$A/";; esac
  [ -n "$n" ] || continue
  if [ "$n" -lt "$MAXIT" ] || { [ "$n" = "$MAXIT" ] && case $b in sizes_*|seed_*) true;; *) false;; esac; }; then cp "$f" "$A/"; fi
done
cp "$A/pinned_$((MAXIT - 1)).txt" "$A/pinned.txt" 2>/dev/null
awk -v m="$MAXIT" '$1 == "it" && $2 + 0 >= m { exit } { print }' "$W/farm/auto/log.txt" > "$A/log.txt"
( cd "$R" && env "$@" CA_JOBS=${CA_JOBS:-2} DRAW_JOBS=${DRAW_JOBS:-2} PNR_TIMEOUT=${PNR_TIMEOUT:-3600} BDC_AUTO_REWRITES=0 \
    AUTO_RESUME="$A" AUTO_OVERBUILD="$H" AUTO_SEARCH=0 research/tools/suite/suite_one.sh "$K" "$S" 4 "$MAXIT" ) > "$W/suite_one.log" 2>&1
cp "$RUNS/suite/${K}_$S/"*.txt "$W/" 2>/dev/null
mkdir -p "$W/auto"; cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$W/auto/" 2>/dev/null
want=$(awk '{print $2}' "$W/farm/auto/it_$MAXIT.txt" 2>/dev/null); got=$(awk '{print $2}' "$W/auto/it_${MAXIT}.txt" 2>/dev/null)
f=$(grep -oE '(status|draws|P|rule|it)=[^ ]*' "$W/farm/result.txt" 2>/dev/null | tr '\n' ' ')
t=$(grep -oE '(status|draws|P|P_untrimmed|trims|rule|it|bits)=[^ ]*' "$W/result.txt" 2>/dev/null | tr '\n' ' ')
echo "$Q $TK $K $S ob$H | it $MAXIT rebuilt sdf ${got:-?} (farm ${want:-?}) | farm: $f| overbuild: ${t:-$(tail -1 "$RUNS/auto/su_${K}_$S/result.txt" 2>/dev/null)} | $(grep -E '^(phase 2|it [0-9]+ (trim check|clean after))' "$RUNS/auto/su_${K}_$S/log.txt" 2>/dev/null | tr '\n' ';')"
if [ "${TRIM_KEEP:-0}" != 1 ]; then rm -rf "$RUNS"; git -C "$R" worktree prune; fi
