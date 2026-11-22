#!/bin/bash
#CLUSTER array=5,9,10,19,21,23,24,25,26,27,28,29,30 cores=4 mem=32G time=240
# suite13t_s5b_mff_2_r1: resumes suite13t_s5b_mff_2's 13 task(s) that ended without a result line (5,9,10,19,21,23,24,25,26,27,28,29,30), from their $SHARED state; the same
# body otherwise (same kernel / seed per task number), 4 cores with the four draws at once.
# 32G: four draws of a large kernel at once were OOM-killed at 16G (v10 nest3 s4). mff_2 task 5 (test_bitint s2) exited 0
# after 28 min with no result line and an empty auto/result.txt (cause not found); it reruns from its state or the top.
# suite13t_s5b_mff_2 (2026-11-20 15:45 UTC; named to run after flow v10's eight parts and before suite13t_s5c_sibb): flow v10
# exactly (suite13t_s5a_v10_*'s environment) plus BDC_MEM_FASTFALL=1, on the 30 suite kernels it changes (every kernel
# with a memory port under BDC_AUTO=1: bdc/mem.py emits cells/rtl/optin/bd_mem_ff.v, the port's two lines rising
# through DSETUP / DCO and falling in one element; research/data/suite/memauto.md section 4 has the safety argument),
# seed 2. The control is v10's same (kernel, seed). Loop state in $SHARED/state_mff.
# Local evidence (one seed each, v9 + trim, through the loop): gather s1 54.19 -> 37.72 ns trimmed (suite13t's route,
# untrimmed and trimmed the same; the FASTFALL loop it 4, 4 / 4 draws), fill s1 30.40 -> 29.81 ns; single routes on the
# base loops' sizes (memauto.md): gather s1 -6.0 %, gather s2 -8.0 %, fill s2 -12.7 %.
# PREDICTION (2026-11-20 15:45 UTC, before any result here; against v10's same kernel and seed, routes clean in both):
# P lower on the kernels whose critical cycle crosses a RAM port's return to zero, median -5 % over the 30, range
# about -30 % .. +3 % (route scatter where the port is off the cycle); every draw passes on every judged route, with no
# RAMB18 setup / hold event in any draw; the rule-clean share within 5 points of v10's on these kernels.
set -uo pipefail
KS=(memsum dot2 gather fill test_bitint unused_arg if_loop_1 if_loop_2 sumi3_mem fir simple_example_1 while_loop_3 if_convert test_memory_1 test_memory_2 test_bool_array binary_search mul_example share_test_2 test_stdint spmv test_flatten_array image_resize vector_rescale stencil_2d iir share_test_1 single_loop loop_path nested_loop)
NK=${#KS[@]}
K=${KS[$(( TASK - 1 ))]}; S=2
export CA_JOBS=2 DRAW_JOBS=4 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle AUTO_RACE_Z=4.5 AUTO_PROVED_RW=cache BDC_MEM_FASTFALL=1
echo "suite13t_s5b_mff_2 kernel $K seed $S (flow v10 + BDC_MEM_FASTFALL=1)" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
# $SHARED state (added 2026-11-20 15:45 UTC, before this request started; the flow is unchanged): suite13t lost ~30 % of
# its tasks to the 240-min limit (13 kernels on every seed so far), most after their loop had shipped. This task's auto/
# files also go to $SHARED/state_mff/K_S every 5 min (non-empty files only, each by rename); a later request with this
# same body (a resume part, filed with the tasks that ran out of time) finds them and goes on: AUTO_RESUME (the loop from
# its last ratchet step, then the search phase and the final stacks again) or, when the loop had finished,
# AUTO_TRIM_ONLY (the shipped route rebuilt from its sizes, seed and structure, checked by sdf md5, trimmed and timed
# again), then the draws. The trim records are dropped first (it_I.txt gets the untrimmed line back: same route, same
# sdf). A task that ends with a result line removes its state.
ST=$SHARED/state_mff/${K}_$S
if [ -f "$ST/sizes_1.vh" ]; then
  mkdir -p "$RUNS/state" && cp "$ST"/* "$RUNS/state/" 2>/dev/null
  for f in "$RUNS/state"/*; do b=${f##*/}
    case $b in it_*_untrimmed.txt) mv "$f" "$RUNS/state/${b%_untrimmed.txt}.txt";; trim_*|sizes_*_trim*|snap_*) rm -f "$f";; esac
  done
  export AUTO_RESUME=$RUNS/state; how="the loop goes on"
  if grep -qE '^(CLEAN|NOT CLEAN)' "$RUNS/state/result.txt" 2>/dev/null; then export AUTO_TRIM_ONLY=1; how="the loop had finished: trim-only"; fi
  echo "resumed from SHARED/state_mff/${K}_$S ($(ls "$RUNS/state" | wc -l) files; $how)" >> "$OUT/task.txt"
fi
mkdir -p "$ST"
save() { cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
  local f; for f in "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh; do
    [ -s "$f" ] && cp "$f" "$ST/.part" 2>/dev/null && mv "$ST/.part" "$ST/${f##*/}"; done; }
( while sleep 300; do save; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null; wait $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
rm -f "$OUT/auto/"place_*.txt
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
it=$(grep -oP 'it=\K[0-9]+' "$OUT/result.txt" 2>/dev/null | head -1)
for c in 0.20 0.31; do
  f=$RUNS/ca/su_${K}_${S}_$it/rule_$c/soak.sdf
  [ -n "$it" ] && [ -f "$f" ] && python3 research/tools/caphold.py "$f" > "$OUT/caphold_$c.txt" 2>&1
done
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
if grep -q "status=" "$OUT/result.txt" 2>/dev/null; then rm -rf "$ST"; else save; fi
exit 0
