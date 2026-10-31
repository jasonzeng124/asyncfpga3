#!/usr/bin/env bash
# Probe XInert (formal/notes/A-xinert.md): pipe3 / ring3 under xaudit --inertial.
#   XAUDIT=<new binary> XAUDIT_BASE=<binary built from the pre-XInert Main/Parse> ./run_small.sh
# Writes results/<case>__<variant>.txt (+ .check.txt for check mode) and results/summary.txt.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE/.."
X="${XAUDIT:?new binary}"
XB="${XAUDIT_BASE:-}"
R="$HERE/results"; mkdir -p "$R"
declare -A CASE=(
  [pipe3_slow]="designs/pipe3.json --stim designs/pipe3.stim.json --bands designs/slow_corner.bands.json"
  [pipe3_holdviol_slow]="designs/pipe3.json --stim designs/pipe3_holdviol.stim.json --bands designs/slow_corner.bands.json"
  [pipe3_slowfb]="designs/pipe3.json --stim designs/pipe3.stim.json --bands designs/slowfb.bands.json"
  [pipe3_default]="designs/pipe3.json --stim designs/pipe3.stim.json"
  [ring3_slow]="designs/ring3.json --stim designs/ring3.stim.json --bands designs/slow_corner.bands.json"
)
declare -A VAR=(
  [rho0]="--rho 0"
  [rho15]="--rho 15"
  [rho50]="--rho 50"
  [dlut]="--rho-lut delay --rho-route 0"
  [dall]="--rho delay"
)
: > "$R/summary.txt"
for c in pipe3_slow pipe3_holdviol_slow pipe3_slowfb pipe3_default ring3_slow; do
  $X ${CASE[$c]} > "$R/${c}__plain.txt"; e=$?
  echo "$c plain: exit $e $(grep SUMMARY "$R/${c}__plain.txt")" >> "$R/summary.txt"
  if [ -n "$XB" ]; then
    $XB ${CASE[$c]} > "$R/${c}__base.txt"
    if cmp -s "$R/${c}__base.txt" "$R/${c}__plain.txt"; then echo "  plain == base binary: IDENTICAL" >> "$R/summary.txt"
    else echo "  plain vs base binary: DIFFER" >> "$R/summary.txt"; fi
  fi
  for v in rho0 rho15 rho50 dlut dall; do
    $X ${CASE[$c]} --inertial check ${VAR[$v]} > "$R/${c}__${v}.check.txt"; ec=$?
    $X ${CASE[$c]} --inertial widen ${VAR[$v]} > "$R/${c}__${v}.txt"; e=$?
    echo "$c $v: check exit $ec $(grep -o 'check REFUSED: [0-9]* gates' "$R/${c}__${v}.check.txt"); widen exit $e $(grep -o 'widened [0-9]* of [0-9]* gates, by up to [0-9]* steps' "$R/${c}__${v}.txt") $(grep SUMMARY "$R/${c}__${v}.txt")" >> "$R/summary.txt"
    if [ $v = rho0 ]; then
      if diff <(grep -v '^inertial (\|^  widened ' "$R/${c}__${v}.txt") "$R/${c}__plain.txt" >/dev/null; then
        echo "  rho0 widen == plain (minus the 2 inertial header lines): IDENTICAL" >> "$R/summary.txt"
      else echo "  rho0 widen vs plain: DIFFER" >> "$R/summary.txt"; fi
    fi
  done
done
cat "$R/summary.txt"
