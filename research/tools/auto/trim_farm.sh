#!/usr/bin/env bash
# trim_farm.sh REQ TASK OUTROOT [ENV...] -- the flow's trim step (auto_size.sh AUTO_TRIM=1) measured on a route a farm
# request already shipped and judged: the task's auto/ files from origin/claude/cluster, the route rebuilt from its own
# sizes and seed (auto_size.sh AUTO_TRIM_ONLY=1: the sdf md5 must be the loop's), trimmed, the full stack, and the
# draws suite_one.sh would run (the same draw points K = 10000 + 100 * SEED + j as the farm's untrimmed run: paired).
# ENV: the request's own environment (e.g. CA_BENCHCAP=1 for suite13 / exit1). The fixture is whatever this checkout's
# build/frontend holds: run it from a worktree whose build/frontend matches the request (exit1: cloud/fixtures/
# frontend_exitcond copied over the default). Writes OUTROOT/REQ_TASK/: farm/ (the task's result and draws as the farm
# returned them), the trimmed run's result.txt, draws.txt, draw_*.txt, auto/{log,it_*,trim_*}.txt; prints one line:
# REQ TASK K S | farm: <its result fields> | trimmed: <suite_one.sh's line> | trim: <the trim step's log lines>.
set -uo pipefail
Q=$1; TK=$2; OR=$(mkdir -p "$3" && cd "$3" && pwd); shift 3
R=$(cd "$(dirname "$0")/../../.." && pwd)
W=$OR/${Q}_$TK; rm -rf "$W"; mkdir -p "$W/farm"
git -C "$R" archive origin/claude/cluster "results/$Q/$TK" 2>/dev/null | tar -x -C "$W/farm" --strip-components=3 \
  || { echo "$Q $TK | no farm files"; exit 1; }
read -r _ _ K _ S _ <<< "$(head -1 "$W/farm/task.txt")"
[ -n "$K" ] && [ -n "$S" ] && [ -f "$W/farm/auto/result.txt" ] || { echo "$Q $TK | no finished loop (task.txt / auto/result.txt)"; exit 1; }
export RUNS=$W/runs; mkdir -p "$RUNS"
cp -r "$W/farm/auto" "$RUNS/farm_auto"
# a request that already ran the trim step (suite13t: AUTO_TRIM=1) left its trim record: drop it, so the step runs afresh
# on the untrimmed route (auto_size.sh re-applies a recorded trim instead of trimming when one is there)
rm -f "$RUNS/farm_auto/"trim_*.txt "$RUNS/farm_auto/"sizes_*_trim*.vh "$RUNS/farm_auto/"it_*_untrimmed.txt "$RUNS/farm_auto/"cyc_*.txt
( cd "$R" && env "$@" CA_JOBS=${CA_JOBS:-2} DRAW_JOBS=${DRAW_JOBS:-2} PNR_TIMEOUT=${PNR_TIMEOUT:-3600} BDC_AUTO_REWRITES=0 \
    AUTO_RESUME="$RUNS/farm_auto" AUTO_TRIM_ONLY=1 research/tools/suite/suite_one.sh "$K" "$S" 4 4 ) > "$W/suite_one.log" 2>&1
cp "$RUNS/suite/${K}_$S/"*.txt "$W/" 2>/dev/null
mkdir -p "$W/auto"; cp "$RUNS/auto/su_${K}_$S/"{log,result}.txt "$RUNS/auto/su_${K}_$S/"it_*.txt "$RUNS/auto/su_${K}_$S/"trim_*.txt \
  "$RUNS/auto/su_${K}_$S/"neg_*t*.txt "$RUNS/auto/su_${K}_$S/"sizes_*_trim.vh "$W/auto/" 2>/dev/null
f=$(cut -d' ' -f3- "$W/farm/result.txt" 2>/dev/null | grep -oE '(status|draws|P|rule|it)=[^ ]*' | tr '\n' ' ')
t=$(cut -d' ' -f3- "$W/result.txt" 2>/dev/null | grep -oE '(status|draws|P|rule|it|bits|sdf)=[^ ]*' | tr '\n' ' ')
echo "$Q $TK $K $S | farm: $f| trimmed: ${t:-$(tail -1 "$RUNS/auto/su_${K}_$S/result.txt" 2>/dev/null)} | $(grep -E '^trim' "$RUNS/auto/su_${K}_$S/log.txt" 2>/dev/null | tr '\n' ';')"
# the route directories are large (routed JSON, bits, SDFs at two corners per trim step): keep the trimmed FASM and the
# trim record, drop the rest unless TRIM_KEEP=1
if [ "${TRIM_KEEP:-0}" != 1 ]; then
  for d in "$RUNS"/hw/su_*; do [ -L "$d" ] && continue; [ -f "$d/${K}_bench_gen.fasm" ] && xz -c "$d/${K}_bench_gen.fasm" > "$W/$(basename "$d").fasm.xz"; done
  rm -rf "$RUNS"; git -C "$R" worktree prune
fi
