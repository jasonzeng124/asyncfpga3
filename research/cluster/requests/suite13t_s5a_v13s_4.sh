#!/bin/bash
#CLUSTER array=1-12 cores=2 mem=16G time=240
# suite13t_s5a_v13s_4: seed 4
# suite13t_s5a_v13s_S: the A/B partner of flow v13 for one question -- does building EVERY route with BD_SYMTRIM
# (link request lines and other symmetric lines become trimmable by LUT INIT, which v11-v13 allow only in the late
# phase) let the cycle-scoped trim recover time that shipped routes keep in link request lines? v13's body and export
# line exactly, plus BD_DEFINES=-DBD_SYMTRIM (the build, trim_lines.py and the rule all read it); state in
# $SHARED/state_v13s. Kernels: the 12 where a flow v10 route kept > 3 % of P in link request lines the rule would
# shorten (research/JOURNAL.md 2026-11-22; sqrtsub s1 75 %, fold64 s1 22 %, ...), seeds 1-4, paired task for task
# with v13's. PREDICTION (written 2026-11-22 before any result): P ratio v13s / v13 over pairs clean in both
# <= 0.98 (geomean), sqrtsub / fold64 / sumi3_mem / dot2 lower on most seeds; no wrong answer; convergence no worse.
set -uo pipefail
KS=(sqrtsub fold64 sumi3_mem dot2 fir collatz fill countloop horner branchloop vector_rescale xorshift)
NK=${#KS[@]}
K=${KS[$(( TASK - 1 ))]}; S=4
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle AUTO_RACE_Z=4.5 AUTO_PROVED_RW=cache AUTO_OVERBUILD=3 AUTO_OVERBUILD_LATE=4 TRIM_STAGEFIX=1 AUTO_RACE_KEEP=1 AUTO_PROVED_RW_CACHE=research/data/autorw/cache_v11.tsv AUTO_LATE_AFTER_SEARCH=1 AUTO_GUARD_E=0.90,1.10 AUTO_RACE_KAPPA=0.13 BDC_MEM_FASTFALL=2 AUTO_TRIM_PORTS=1 AUTO_CKPT=1 AUTO_SEARCH_KEEPDEPTH=1 AUTO_SEARCH_OVERBUILD=4 BDC_SHIFT_MASK=1 BD_DEFINES=-DBD_SYMTRIM
echo "suite13t_s5a_v13 kernel $K seed $S (flow v13 + BD_SYMTRIM everywhere)" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
# $SHARED state (added 2026-11-20 15:45 UTC, before this request started; the flow is unchanged): suite13t lost ~30 % of
# its tasks to the 240-min limit (13 kernels on every seed so far), most after their loop had shipped. This task's auto/
# files also go to $SHARED/state_v13s/K_S every 5 min (non-empty files only, each by rename); a later request with this
# same body (a resume part, filed with the tasks that ran out of time) finds them and goes on: AUTO_RESUME (the loop from
# its last ratchet step, then the search phase and the final stacks again) or, when the loop had finished,
# AUTO_TRIM_ONLY (the shipped route rebuilt from its sizes, seed and structure, checked by sdf md5, trimmed and timed
# again), then the draws. The trim records are dropped first (it_I.txt gets the untrimmed line back: same route, same
# sdf). A task that ends with a result line removes its state.
ST=$SHARED/state_v13s/${K}_$S
if [ -f "$ST/sizes_1.vh" ]; then
  mkdir -p "$RUNS/state" && cp "$ST"/* "$RUNS/state/" 2>/dev/null
  for f in "$RUNS/state"/*; do b=${f##*/}
    case $b in it_*_untrimmed.txt) mv "$f" "$RUNS/state/${b%_untrimmed.txt}.txt";; trim_*|sizes_*_trim*|snap_*) rm -f "$f";; esac
  done
  export AUTO_RESUME=$RUNS/state; how="the loop goes on"
  if grep -qE '^(CLEAN|NOT CLEAN)' "$RUNS/state/result.txt" 2>/dev/null; then export AUTO_TRIM_ONLY=1; how="the loop had finished: trim-only"; fi
  echo "resumed from SHARED/state_v13s/${K}_$S ($(ls "$RUNS/state" | wc -l) files; $how)" >> "$OUT/task.txt"
fi
mkdir -p "$ST"
save() { cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
  rm -f "$OUT/auto/"stk_*.txt "$OUT/auto/"rck_*.txt "$OUT/auto/"dck_*.txt
  local f; for f in "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh; do
    [ -s "$f" ] && cp "$f" "$ST/.part" 2>/dev/null && mv "$ST/.part" "$ST/${f##*/}"; done; }
( while sleep 300; do save; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null; wait $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
rm -f "$OUT/auto/"place_*.txt "$OUT/auto/"stk_*.txt "$OUT/auto/"rck_*.txt "$OUT/auto/"dck_*.txt
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
it=$(grep -oP 'it=\K[0-9]+' "$OUT/result.txt" 2>/dev/null | head -1)
for c in 0.20 0.31; do
  f=$RUNS/ca/su_${K}_${S}_$it/rule_$c/soak.sdf
  [ -n "$it" ] && [ -f "$f" ] && python3 research/tools/caphold.py "$f" > "$OUT/caphold_$c.txt" 2>&1
done
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
if grep -q "status=" "$OUT/result.txt" 2>/dev/null; then rm -rf "$ST"; else save; fi
exit 0
